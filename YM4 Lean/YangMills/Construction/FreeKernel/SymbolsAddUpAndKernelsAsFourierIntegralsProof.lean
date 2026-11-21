import YangMills.Construction.FreeKernel.SymbolDerivativeEstimates
import YangMills.Construction.FreeKernel.SymbolsAddUpAndKernelsAsFourierIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex LatticeKernel MeasureTheory
theorem laplacianSymbol_eq_four_sin_sq (θ : ℝ) : laplacianSymbol θ = 4 * Real.sin (θ / 2) ^ 2 := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.laplacianSymbol_eq_four_sin_sq <;> assumption
theorem gaussianHeatKernel4_eq (t : ℝ) (x : Fin 4 → ℝ) (ht : 0 < t) :
    FourDimKernel.gaussianHeatKernel4 t x =
      (4 * Real.pi * t) ^ (-2 : ℤ) *
        Real.exp (-FourDimKernel.realVecNorm x ^ 2 / (4 * t)) := by
  have hpos : 0 < 4 * Real.pi * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * t) ^ 2 = 4 * Real.pi * t := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (4 * Real.pi * t) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hnorm : FourDimKernel.realVecNorm x ^ 2 =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
    have hnn : 0 ≤ FourVector.inner4 x x := by
      unfold FourVector.inner4
      exact Finset.sum_nonneg fun μ _ => mul_self_nonneg _
    unfold FourDimKernel.realVecNorm FourVector.euclidNorm
    rw [Real.sq_sqrt hnn]
    unfold FourVector.inner4
    rw [Fin.sum_univ_four]
    ring
  have hzp : (4 * Real.pi * t) ^ (-2 : ℤ) = 1 / Real.sqrt (4 * Real.pi * t) ^ 4 := by
    have h4 : Real.sqrt (4 * Real.pi * t) ^ 4 = (4 * Real.pi * t) ^ 2 := by
      rw [show ∀ r : ℝ, r ^ 4 = (r ^ 2) ^ 2 from fun r => by ring, hsq]
    rw [h4, zpow_neg, one_div]
    norm_cast
  unfold FourDimKernel.gaussianHeatKernel4 LatticeKernel.gaussianHeatKernel
  rw [Fin.prod_univ_four, hnorm, hzp]
  have hsplit : Real.exp (-(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) / (4 * t)) =
      Real.exp (-x 0 ^ 2 / (4 * t)) * Real.exp (-x 1 ^ 2 / (4 * t)) *
        Real.exp (-x 2 ^ 2 / (4 * t)) * Real.exp (-x 3 ^ 2 / (4 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  generalize Real.sqrt (4 * Real.pi * t) = r at hne
  field_simp
theorem symbolRelations_holds : SymbolRelations := by
  refine ⟨laplacianSymbol_eq_four_sin_sq, fun k => ?_, fun θ => ?_, fun θ => ?_, fun t x ht =>
    gaussianHeatKernel4_eq t x ht⟩
  · unfold PeriodicLattice.ShortDistanceTwoPoint.laplacianSymbol
    exact Finset.sum_congr rfl fun μ _ => (laplacianSymbol_eq_four_sin_sq (k μ)).symm
  · simp [homotopySymbol]
  · simp [homotopySymbol, symbolError]
def gaussFourierIntegrand (n : ℕ) (t ξ θ : ℝ) : ℂ :=
  Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (I * (θ : ℂ)) ^ n * (Real.exp (-t * θ ^ 2) : ℂ)
theorem continuous_gaussFourierIntegrand (n : ℕ) (t ξ : ℝ) :
    Continuous (gaussFourierIntegrand n t ξ) := by
  unfold gaussFourierIntegrand
  have hg : Continuous fun θ : ℝ => ((Real.exp (-t * θ ^ 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  exact (by fun_prop : Continuous fun θ : ℝ =>
    Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (I * (θ : ℂ)) ^ n).mul hg
theorem norm_gaussFourierIntegrand (n : ℕ) (t ξ θ : ℝ) :
    ‖gaussFourierIntegrand n t ξ θ‖ = |θ| ^ n * Real.exp (-t * θ ^ 2) := by
  have hrw : I * (ξ : ℂ) * (θ : ℂ) = ((ξ * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold gaussFourierIntegrand
  rw [norm_mul, norm_mul, hrw, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
theorem integrable_abs_pow_mul_exp_neg_mul_sq {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable fun θ : ℝ => |θ| ^ n * Real.exp (-t * θ ^ 2) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq ht
    (s := (n : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm
  refine hi.congr (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Real.rpow_natCast, norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_pos (Real.exp_pos _)]
theorem integrable_gaussFourierIntegrand {t : ℝ} (ht : 0 < t) (n : ℕ) (ξ : ℝ) :
    Integrable (gaussFourierIntegrand n t ξ) := by
  refine (integrable_abs_pow_mul_exp_neg_mul_sq ht n).mono'
    (continuous_gaussFourierIntegrand n t ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => (norm_gaussFourierIntegrand n t ξ θ).le)
theorem hasDerivAt_gaussFourierIntegrand (n : ℕ) (t y θ : ℝ) :
    HasDerivAt (fun z : ℝ => gaussFourierIntegrand n t z θ)
      (gaussFourierIntegrand (n + 1) t y θ) y := by
  have ha : HasDerivAt (fun z : ℝ => I * (z : ℂ) * (θ : ℂ)) (I * (θ : ℂ)) y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.const_mul I).mul_const (θ : ℂ)
  have hb := (ha.cexp.mul_const ((I * (θ : ℂ)) ^ n)).mul_const ((Real.exp (-t * θ ^ 2) : ℂ))
  exact hb.congr_deriv (by unfold gaussFourierIntegrand; ring)
theorem hasDerivAt_integral_gaussFourierIntegrand {t : ℝ} (ht : 0 < t) (n : ℕ) (ξ : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ θ : ℝ, gaussFourierIntegrand n t y θ)
      (∫ θ : ℝ, gaussFourierIntegrand (n + 1) t ξ θ) ξ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := ξ) (s := Set.univ)
    (F := fun y θ => gaussFourierIntegrand n t y θ)
    (F' := fun y θ => gaussFourierIntegrand (n + 1) t y θ)
    (bound := fun θ => |θ| ^ (n + 1) * Real.exp (-t * θ ^ 2))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      (continuous_gaussFourierIntegrand n t y).aestronglyMeasurable)
    (integrable_gaussFourierIntegrand ht n ξ)
    (continuous_gaussFourierIntegrand (n + 1) t ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ y _ => (norm_gaussFourierIntegrand (n + 1) t y θ).le)
    (integrable_abs_pow_mul_exp_neg_mul_sq ht (n + 1))
    (Filter.Eventually.of_forall fun θ y _ => hasDerivAt_gaussFourierIntegrand n t y θ)).2
theorem one_div_sqrt_four_pi_mul_eq {t : ℝ} (ht : 0 < t) :
    1 / Real.sqrt (4 * Real.pi * t) = 1 / (2 * Real.pi) * Real.sqrt (Real.pi / t) := by
  have hmul : Real.sqrt (4 * Real.pi * t) * Real.sqrt (Real.pi / t) = 2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity), show 4 * Real.pi * t * (Real.pi / t) = (2 * Real.pi) ^ 2 by
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have hne : Real.sqrt (4 * Real.pi * t) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [← hmul]
  field_simp
theorem gaussianHeatKernel_eq_fourierIntegral {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    ((gaussianHeatKernel t ξ : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (Real.exp (-t * θ ^ 2) : ℂ) := by
  have hre : 0 < ((t : ℂ)).re := by simpa using ht
  have hft := fourierIntegral_gaussian hre (ξ : ℂ)
  have hint : (∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (Real.exp (-t * θ ^ 2) : ℂ)) =
      ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * Complex.exp (-(t : ℂ) * (θ : ℂ) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Complex.ofReal_exp]
    push_cast
    rfl
  have hcpow : ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hcexp : Complex.exp (-(ξ : ℂ) ^ 2 / (4 * (t : ℂ))) =
      ((Real.exp (-ξ ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  rw [hint, hft, hcpow, hcexp]
  unfold gaussianHeatKernel
  rw [div_eq_mul_one_div, one_div_sqrt_four_pi_mul_eq ht]
  push_cast
  ring
theorem iteratedDeriv_gaussianHeatKernel_eq_fourierIntegral {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∀ ξ : ℝ, ((iteratedDeriv n (gaussianHeatKernel t) ξ : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ θ : ℝ, gaussFourierIntegrand n t ξ θ := by
  induction n with
  | zero =>
    intro ξ
    rw [iteratedDeriv_zero, gaussianHeatKernel_eq_fourierIntegral ht]
    simp [gaussFourierIntegrand]
  | succ n ih =>
    intro ξ
    set D : ℂ := (1 / (2 * (Real.pi : ℂ))) * ∫ θ : ℝ, gaussFourierIntegrand (n + 1) t ξ θ with hD
    have hc : HasDerivAt (fun y : ℝ => ((iteratedDeriv n (gaussianHeatKernel t) y : ℝ) : ℂ)) D ξ := by
      have hd := (hasDerivAt_integral_gaussFourierIntegrand ht n ξ).const_mul
        (1 / (2 * (Real.pi : ℂ)))
      exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih)
    have hre : HasDerivAt (iteratedDeriv n (gaussianHeatKernel t)) D.re ξ := by
      have hd : HasDerivAt (fun y : ℝ => ((iteratedDeriv n (gaussianHeatKernel t) y : ℝ) : ℂ).re)
          D.re ξ := Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ hc
      simpa only [Complex.ofReal_re] using hd
    have him : D.im = 0 := by
      have hd : HasDerivAt (fun y : ℝ => ((iteratedDeriv n (gaussianHeatKernel t) y : ℝ) : ℂ).im)
          D.im ξ := Complex.imCLM.hasFDerivAt.comp_hasDerivAt ξ hc
      simp only [Complex.ofReal_im] at hd
      exact hd.unique (hasDerivAt_const ξ 0)
    rw [iteratedDeriv_succ, hre.deriv]
    exact Complex.ext (by simp) (by simp [him])
def circleFourierCoeff (σ : ℝ → ℂ) (j : ℤ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * σ θ
theorem intervalIntegrable_cexp_mul {σ : ℝ → ℂ} (hσ : Continuous σ) (j : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) * σ θ) volume a b :=
  ((by fun_prop : Continuous fun θ : ℝ => Complex.exp (I * (j : ℂ) * (θ : ℂ))).mul
    hσ).intervalIntegrable a b
theorem cexp_int_add_one_mul (j : ℤ) (θ : ℝ) :
    Complex.exp (I * ((j + 1 : ℤ) : ℂ) * (θ : ℂ)) =
      Complex.exp (I * (j : ℂ) * (θ : ℂ)) * Complex.exp (I * (θ : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem cexp_int_sub_one_mul (j : ℤ) (θ : ℝ) :
    Complex.exp (I * ((j - 1 : ℤ) : ℂ) * (θ : ℂ)) =
      Complex.exp (I * (j : ℂ) * (θ : ℂ)) * Complex.exp (-(I * (θ : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem fwdDiff_circleFourierCoeff {σ : ℝ → ℂ} (hσ : Continuous σ) :
    LatticeKernel.fwdDiff (circleFourierCoeff σ) =
      circleFourierCoeff fun θ => (Complex.exp (I * (θ : ℂ)) - 1) * σ θ := by
  funext j
  unfold LatticeKernel.fwdDiff circleFourierCoeff
  rw [← mul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_cexp_mul hσ _ _ _)
    (intervalIntegrable_cexp_mul hσ _ _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [cexp_int_add_one_mul]
  ring
theorem bwdDiff_circleFourierCoeff {σ : ℝ → ℂ} (hσ : Continuous σ) :
    bwdDiff (circleFourierCoeff σ) =
      circleFourierCoeff fun θ => (1 - Complex.exp (-(I * (θ : ℂ)))) * σ θ := by
  funext j
  unfold bwdDiff circleFourierCoeff
  rw [← mul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_cexp_mul hσ _ _ _)
    (intervalIntegrable_cexp_mul hσ _ _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [cexp_int_sub_one_mul]
  ring
theorem fwd_mul_bwd_multiplier_eq (θ : ℝ) :
    (Complex.exp (I * (θ : ℂ)) - 1) * (1 - Complex.exp (-(I * (θ : ℂ)))) =
      -(laplacianSymbol θ : ℂ) := by
  have hinv : Complex.exp (I * (θ : ℂ)) * Complex.exp (-(I * (θ : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hcos : (2 : ℂ) * Complex.cos (θ : ℂ) =
      Complex.exp (I * (θ : ℂ)) + Complex.exp (-(I * (θ : ℂ))) := by
    rw [Complex.cos]
    rw [show (θ : ℂ) * I = I * (θ : ℂ) by ring, show -(θ : ℂ) * I = -(I * (θ : ℂ)) by ring]
    ring
  unfold laplacianSymbol
  push_cast
  linear_combination (-1 : ℂ) * hinv - hcos
theorem continuous_heatSymbolFactor (t : ℝ) :
    Continuous fun θ : ℝ => ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ) := by
  unfold laplacianSymbol
  exact Complex.continuous_ofReal.comp (by fun_prop)
theorem discreteHeatKernel_eq_circleFourierCoeff (t : ℝ) :
    discreteHeatKernel t =
      circleFourierCoeff fun θ => ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ) :=
  rfl
theorem diffOp_discreteHeatKernel (t : ℝ) (j : ℤ) (α : DiffKind) :
    diffOp α (discreteHeatKernel t) j =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ θ in (-Real.pi)..Real.pi,
          Complex.exp (I * (j : ℂ) * (θ : ℂ)) * diffMultiplier α θ *
            (Real.exp (-t * laplacianSymbol θ) : ℂ) := by
  have hσ := continuous_heatSymbolFactor t
  rw [discreteHeatKernel_eq_circleFourierCoeff]
  cases α with
  | identity =>
    simp only [diffOp, diffMultiplier, mul_one]
    rfl
  | forward =>
    simp only [diffOp, diffMultiplier]
    rw [fwdDiff_circleFourierCoeff hσ]
    unfold circleFourierCoeff
    simp only [mul_assoc]
  | backward =>
    simp only [diffOp, diffMultiplier]
    rw [bwdDiff_circleFourierCoeff hσ]
    unfold circleFourierCoeff
    simp only [mul_assoc]
  | laplacian =>
    simp only [diffOp, diffMultiplier]
    have hσ' : Continuous fun θ : ℝ => (1 - Complex.exp (-(I * (θ : ℂ)))) *
        ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ) :=
      (by fun_prop : Continuous fun θ : ℝ => 1 - Complex.exp (-(I * (θ : ℂ)))).mul hσ
    rw [bwdDiff_circleFourierCoeff hσ, fwdDiff_circleFourierCoeff hσ']
    unfold circleFourierCoeff
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only []
    rw [← fwd_mul_bwd_multiplier_eq]
    ring
theorem fourierIntegralForms_holds : FourierIntegralForms := by
  intro t ht j ξ α
  refine ⟨gaussianHeatKernel_eq_fourierIntegral ht ξ, diffOp_discreteHeatKernel t j α, ?_⟩
  have hd := iteratedDeriv_gaussianHeatKernel_eq_fourierIntegral ht (diffOrder α) ξ
  unfold gaussianHeatKernelDeriv
  rw [hd]
  rfl
theorem symbolsAndFourierIntegrals_holds : symbolsAndFourierIntegrals :=
  ⟨symbolRelations_holds, fourierIntegralForms_holds⟩
end YangMills.Construction.FreeKernel
end
