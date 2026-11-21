import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.FreeKernel.GaussianTimesVanishingFunction
import YangMills.Construction.FreeKernel.LatticeGaussianPeriodDifference
import YangMills.Construction.FreeKernel.SymbolDerivativeEstimates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.LatticeGaussianPeriod
open Complex MeasureTheory YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
open scoped ContDiff
lemma natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
lemma hasDerivAt_section_of_contDiff_prod {G : ℝ → ℝ → ℂ}
    (hG : ContDiff ℝ ∞ fun p : ℝ × ℝ => G p.1 p.2) (ς x : ℝ) :
    HasDerivAt (G ς) (fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (ς, x) ((0 : ℝ), (1 : ℝ))) x := by
  have hF : HasFDerivAt (fun p : ℝ × ℝ => G p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (ς, x)) (ς, x) :=
    ((hG.differentiable (by simp)) (ς, x)).hasFDerivAt
  have hl : HasDerivAt (fun y : ℝ => (ς, y)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x ς).prodMk (hasDerivAt_id x)
  exact hF.comp_hasDerivAt x hl
lemma contDiff_partialDeriv_snd {G : ℝ → ℝ → ℂ}
    (hG : ContDiff ℝ ∞ fun p : ℝ × ℝ => G p.1 p.2) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => deriv (G p.1) p.2 := by
  have he : (fun p : ℝ × ℝ => deriv (G p.1) p.2) =
      fun p => fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) p ((0 : ℝ), (1 : ℝ)) := by
    funext p
    exact (hasDerivAt_section_of_contDiff_prod hG p.1 p.2).deriv
  rw [he]
  exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
lemma hasDerivAt_intervalIntegral_unit {G : ℝ → ℝ → ℂ}
    (hG : ContDiff ℝ ∞ fun p : ℝ × ℝ => G p.1 p.2) (θ : ℝ) :
    HasDerivAt (fun x => ∫ ς in (0 : ℝ)..1, G ς x) (∫ ς in (0 : ℝ)..1, deriv (G ς) θ) θ := by
  have hc : Continuous fun p : ℝ × ℝ => G p.1 p.2 := hG.continuous
  have hc' : Continuous fun p : ℝ × ℝ => deriv (G p.1) p.2 :=
    (contDiff_partialDeriv_snd hG).continuous
  have hsec : ∀ x : ℝ, Continuous fun ς : ℝ => G ς x := fun x =>
    hc.comp (continuous_id.prodMk continuous_const)
  have hsec' : ∀ x : ℝ, Continuous fun ς : ℝ => deriv (G ς) x := fun x =>
    hc'.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall θ 1)).exists_bound_of_continuousOn hc'.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x ς => G ς x) (F' := fun x ς => deriv (G ς) x) (bound := fun _ => C)
    (s := Metric.closedBall θ 1) (Metric.closedBall_mem_nhds θ one_pos)
    (Filter.Eventually.of_forall fun x => (hsec x).aestronglyMeasurable)
    ((hsec θ).intervalIntegrable _ _) (hsec' θ).aestronglyMeasurable
    (ae_of_all _ fun ς hς x hx => ?_) intervalIntegrable_const
    (ae_of_all _ fun ς _ x _ => ?_)).2
  · rw [Set.uIoc_of_le zero_le_one] at hς
    exact hC (ς, x) ⟨Set.Ioc_subset_Icc_self hς, hx⟩
  · exact ((hasDerivAt_section_of_contDiff_prod hG ς x).differentiableAt).hasDerivAt
lemma iteratedDeriv_intervalIntegral_unit (n : ℕ) : ∀ {G : ℝ → ℝ → ℂ},
    (ContDiff ℝ ∞ fun p : ℝ × ℝ => G p.1 p.2) → ∀ θ : ℝ,
    iteratedDeriv n (fun x => ∫ ς in (0 : ℝ)..1, G ς x) θ =
      ∫ ς in (0 : ℝ)..1, iteratedDeriv n (G ς) θ := by
  induction n with
  | zero =>
    intro G _ θ
    simp
  | succ m ih =>
    intro G hG θ
    have hd : deriv (fun x => ∫ ς in (0 : ℝ)..1, G ς x) =
        fun x => ∫ ς in (0 : ℝ)..1, deriv (G ς) x :=
      funext fun x => (hasDerivAt_intervalIntegral_unit hG x).deriv
    rw [iteratedDeriv_succ', hd, ih (G := fun ς => deriv (G ς)) (contDiff_partialDeriv_snd hG)]
    simp only [iteratedDeriv_succ']
lemma iteratedDeriv_ofReal_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (κ : ℕ) :
    iteratedDeriv κ (fun x => (g x : ℂ)) = fun x => ((iteratedDeriv κ g x : ℝ) : ℂ) := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.iteratedDeriv_ofReal_comp <;> assumption
lemma contDiff_symbolError : ContDiff ℝ ∞ symbolError := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.contDiff_symbolError <;> assumption
lemma contDiff_realToComplex : ContDiff ℝ ∞ fun x : ℝ => (x : ℂ) :=
  ofRealCLM.contDiff
lemma contDiff_imagMonomial (α : DiffKind) :
    ContDiff ℝ ∞ fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α :=
  (contDiff_const.mul contDiff_realToComplex).pow _
lemma contDiff_diffMultiplier (α : DiffKind) : ContDiff ℝ ∞ (diffMultiplier α) := by
  have h := contDiff_realToComplex
  cases α with
  | identity => exact contDiff_const
  | forward =>
    exact ((contDiff_const.mul h).cexp).sub contDiff_const
  | backward =>
    exact contDiff_const.sub ((contDiff_const.mul h).neg.cexp)
  | laplacian =>
    have hl : ContDiff ℝ ∞ laplacianSymbol := by
      unfold laplacianSymbol
      fun_prop
    exact (ofRealCLM.contDiff.comp hl).neg
lemma contDiff_multiplierError (α : DiffKind) :
    ContDiff ℝ ∞ (multiplierError α) :=
  (contDiff_diffMultiplier α).sub (contDiff_imagMonomial α)
def homotopyExp (t ς x : ℝ) : ℂ :=
  (Real.exp (-t * homotopySymbol ς x) : ℂ)
def imagMonomialSymbolError (α : DiffKind) (x : ℝ) : ℂ :=
  (I * (x : ℂ)) ^ diffOrder α * (symbolError x : ℂ)
lemma contDiff_real_homotopyExp (t ς : ℝ) :
    ContDiff ℝ ∞ fun x => Real.exp (-t * homotopySymbol ς x) := by
  have h := contDiff_symbolError
  unfold homotopySymbol
  fun_prop
lemma contDiff_homotopyExp_prod (t : ℝ) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => homotopyExp t p.1 p.2 := by
  have h := contDiff_symbolError
  have h2 : ContDiff ℝ ∞ fun p : ℝ × ℝ => Real.exp (-t * homotopySymbol p.1 p.2) := by
    unfold homotopySymbol
    fun_prop
  exact ofRealCLM.contDiff.comp h2
lemma contDiff_homotopyExp (t ς : ℝ) : ContDiff ℝ ∞ (homotopyExp t ς) :=
  ofRealCLM.contDiff.comp (contDiff_real_homotopyExp t ς)
lemma contDiff_imagMonomialSymbolError (α : DiffKind) :
    ContDiff ℝ ∞ (imagMonomialSymbolError α) :=
  (contDiff_imagMonomial α).mul (ofRealCLM.contDiff.comp contDiff_symbolError)
lemma homotopyExp_one_sub_zero (t x : ℝ) :
    homotopyExp t 1 x - homotopyExp t 0 x =
      ∫ ς in (0 : ℝ)..1, ((-t * symbolError x : ℝ) : ℂ) * homotopyExp t ς x := by
  have hd : ∀ ς ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun ς => homotopyExp t ς x)
      (((-t * symbolError x : ℝ) : ℂ) * homotopyExp t ς x) ς := by
    intro ς _
    have h1 : HasDerivAt (fun ς => -t * homotopySymbol ς x) (-t * symbolError x) ς := by
      unfold homotopySymbol
      have := (((hasDerivAt_id ς).mul_const (symbolError x)).const_add (x ^ 2)).const_mul (-t)
      simpa using this
    have h2 := h1.exp.ofReal_comp
    refine h2.congr_deriv ?_
    simp only [homotopyExp]
    push_cast
    ring
  have hc : Continuous fun ς : ℝ => ((-t * symbolError x : ℝ) : ℂ) * homotopyExp t ς x :=
    continuous_const.mul
      ((contDiff_homotopyExp_prod t).continuous.comp (continuous_id.prodMk continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
lemma lintegral_rpow_mul_gaussian_half {t : ℝ} (ht : 1 ≤ t) (p : ℝ) :
    ∫⁻ θ : ℝ, ENNReal.ofReal (t ^ p * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) =
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * t ^ (p - 1 / 2)) := by
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_pos
  have hc : 0 < heatDecay := by
    unfold heatDecay
    positivity
  have hlam : 0 < 1 / 2 * heatDecay * t := by positivity
  have hform : ∀ θ : ℝ, -(1 / 2 * heatDecay * t * θ ^ 2) = -(1 / 2 * heatDecay * t) * θ ^ 2 := by
    intro θ
    ring
  have hint : Integrable fun θ : ℝ =>
      t ^ p * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)) := by
    simp_rw [hform]
    exact (integrable_exp_neg_mul_sq hlam).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => by positivity)]
  congr 1
  have hval : Real.pi / (1 / 2 * heatDecay * t) = Real.pi ^ 3 / t := by
    unfold heatDecay
    field_simp
  have hroot : (Real.pi ^ 3) ^ ((1 : ℝ) / 2) = Real.pi ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast Real.pi 3, ← Real.rpow_mul hpi.le]
    norm_num
  simp_rw [hform]
  rw [integral_const_mul, integral_gaussian, hval, Real.sqrt_eq_rpow,
    Real.div_rpow (by positivity) ht0.le, hroot, Real.rpow_sub ht0]
  ring
lemma enorm_ofReal_eq (r : ℝ) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
lemma enorm_iteratedDeriv_homotopyExp_le (hExp : ExpSymbolDerivativeBounds)
    {t ς θ : ℝ} (ht : 1 ≤ t) (hς : ς ∈ Set.Icc (0 : ℝ) 1)
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) (κ : ℕ) :
    ‖iteratedDeriv κ (homotopyExp t ς) θ‖ₑ ≤
      weightedFactorialPower κ *
        ENNReal.ofReal (t ^ ((κ : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) := by
  obtain ⟨h1, h2⟩ := hExp κ t ς θ (Or.inl ⟨ht, hς.1, hς.2, abs_le.2 hθ⟩)
  have he : homotopyExp t ς = fun x => ((Real.exp (-t * homotopySymbol ς x) : ℝ) : ℂ) := rfl
  rw [he, iteratedDeriv_ofReal_comp (contDiff_real_homotopyExp t ς)]
  show ‖((iteratedDeriv κ (fun x => Real.exp (-t * homotopySymbol ς x)) θ : ℝ) : ℂ)‖ₑ ≤ _
  rw [enorm_ofReal_eq]
  exact (ENNReal.ofReal_le_ofReal h1).trans h2
lemma iteratedDeriv_mul_gaussian_bounds (hProd : VanishingTimesGaussianBound) {n b : ℕ}
    {M t : ℝ} {ρ e : ℝ → ℂ} (hM : 0 ≤ M) (ht : 1 ≤ t) (hρ : ContDiff ℝ ∞ ρ)
    (he : ContDiff ℝ ∞ e)
    (hbρ : ∀ κ : ℕ, κ ≤ n → ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖iteratedDeriv κ ρ θ‖ ≤ M * |θ| ^ (b - κ))
    (hbe : ∀ κ : ℕ, κ ≤ n → ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖iteratedDeriv κ e θ‖ₑ ≤
        weightedFactorialPower κ *
          ENNReal.ofReal (t ^ ((κ : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) :
    (∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖iteratedDeriv n (fun x => ρ x * e x) θ‖ₑ ≤
        ENNReal.ofReal M * binomialMoment n b *
          ENNReal.ofReal
            (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) ∧
    ∫⁻ θ in Set.Icc (-Real.pi) Real.pi, ‖iteratedDeriv n (fun x => ρ x * e x) θ‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal M * binomialMoment n b *
        ENNReal.ofReal (t ^ (((n : ℝ) - b - 1) / 2)) := by
  have hU : UniqueDiffOn ℝ (Set.Icc (-Real.pi) Real.pi) :=
    uniqueDiffOn_Icc (by linarith [Real.pi_pos])
  have hw : ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ (κ : ℕ) (θ : ℝ),
      θ ∈ Set.Icc (-Real.pi) Real.pi →
      iteratedDerivWithin κ f (Set.Icc (-Real.pi) Real.pi) θ = iteratedDeriv κ f θ :=
    fun hf κ θ hθ =>
      iteratedDerivWithin_eq_iteratedDeriv hU (hf.of_le (natCast_le_infty κ)).contDiffAt hθ
  have hρe : ContDiff ℝ ∞ fun x => ρ x * e x := hρ.mul he
  obtain ⟨h1, h2⟩ := hProd n b M t _ ρ e hM ht Set.ordConnected_Icc
    (hρ.of_le (natCast_le_infty n)).contDiffOn (he.of_le (natCast_le_infty n)).contDiffOn
    (fun κ hκ θ hθ => by
      rw [hw hρ κ θ hθ, hw he κ θ hθ]
      exact ⟨hbρ κ hκ θ hθ, hbe κ hκ θ hθ⟩)
  refine ⟨fun θ hθ => ?_, ?_⟩
  · rw [← hw hρe n θ hθ]
    exact h1 θ hθ
  · refine le_trans (le_of_eq ?_) h2
    refine setLIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show ‖iteratedDeriv n (fun x => ρ x * e x) θ‖ₑ = _
    rw [hw hρe n θ hθ]
lemma symbol_difference_eq_homotopy (α : DiffKind) (t x : ℝ) :
    diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
        (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ) =
      multiplierError α x * homotopyExp t 1 x -
        ∫ ς in (0 : ℝ)..1, (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x) := by
  have h1 : homotopyExp t 1 x = (Real.exp (-t * laplacianSymbol x) : ℂ) := by
    have h : homotopySymbol 1 x = laplacianSymbol x := by
      unfold homotopySymbol symbolError
      ring
    rw [homotopyExp, h]
  have h0 : homotopyExp t 0 x = (Real.exp (-t * x ^ 2) : ℂ) := by
    have h : homotopySymbol 0 x = x ^ 2 := by
      unfold homotopySymbol
      ring
    rw [homotopyExp, h]
  have hI : (∫ ς in (0 : ℝ)..1, (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x)) =
      -(I * (x : ℂ)) ^ diffOrder α *
        ∫ ς in (0 : ℝ)..1, ((-t * symbolError x : ℝ) : ℂ) * homotopyExp t ς x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ς _ => ?_
    simp only [imagMonomialSymbolError]
    push_cast
    ring
  rw [hI, ← homotopyExp_one_sub_zero, h1, h0]
  unfold multiplierError
  ring
lemma contDiff_homotopyIntegrand_prod (α : DiffKind) (t : ℝ) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      (t : ℂ) * (imagMonomialSymbolError α p.2 * homotopyExp t p.1 p.2) :=
  contDiff_const.mul
    (((contDiff_imagMonomialSymbolError α).comp contDiff_snd).mul (contDiff_homotopyExp_prod t))
lemma enorm_iteratedDeriv_homotopyIntegrand_le (hExp : ExpSymbolDerivativeBounds)
    (hProd : VanishingTimesGaussianBound)
    (hMono : MonomialFactorDerivativeBounds)
    (n : ℕ) (α : DiffKind) {t ς θ : ℝ} (ht : 1 ≤ t) (hς : ς ∈ Set.Icc (0 : ℝ) 1)
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    ‖iteratedDeriv n
        (fun x => (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x)) θ‖ₑ ≤
      ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
        binomialMoment n (diffOrder α + 4) *
        ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
          Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) := by
  have ht0 : 0 < t := by linarith
  have hCsy : 0 ≤ symmetryConstant := by
    unfold symmetryConstant
    positivity
  have hcd : ContDiffAt ℝ n
      (fun x => imagMonomialSymbolError α x * homotopyExp t ς x) θ :=
    (((contDiff_imagMonomialSymbolError α).mul (contDiff_homotopyExp t ς)).of_le
      (natCast_le_infty n)).contDiffAt
  have hsm := iteratedDeriv_fun_const_smul (n := n)
    (f := fun x => imagMonomialSymbolError α x * homotopyExp t ς x) (x := θ) hcd (t : ℂ)
  simp only [smul_eq_mul] at hsm
  rw [hsm, enorm_mul, enorm_ofReal_eq, abs_of_pos ht0]
  gcongr
  exact (iteratedDeriv_mul_gaussian_bounds hProd (by positivity) ht
    (contDiff_imagMonomialSymbolError α)
    (contDiff_homotopyExp t ς) (fun κ hκ θ hθ => hMono.2 α n κ hκ θ hθ)
    (fun κ _ θ hθ => enorm_iteratedDeriv_homotopyExp_le hExp ht hς hθ κ)).1 θ hθ
lemma enorm_intervalIntegral_unit_le {u : ℝ → ℂ} {B : ENNReal}
    (h : ∀ ς ∈ Set.Icc (0 : ℝ) 1, ‖u ς‖ₑ ≤ B) : ‖∫ ς in (0 : ℝ)..1, u ς‖ₑ ≤ B := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (setLIntegral_mono' measurableSet_Ioc
    (fun ς hς => h ς (Set.Ioc_subset_Icc_self hς))).trans ?_
  simp
theorem latticeGaussianDifferenceOnPeriod_holds (hSym : SymbolDerivativeBounds)
    (hProd : VanishingTimesGaussianBound)
    (hMono : MonomialFactorDerivativeBounds) : LatticeGaussianDifferenceOnPeriod := by
  intro n α t ht
  obtain ⟨-, -, -, ⟨-, -, hMult⟩, hExp⟩ := hSym
  have ht0 : 0 < t := by linarith
  have hCsy : 0 ≤ symmetryConstant := by
    unfold symmetryConstant
    positivity
  have hf : (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
        (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) =
      fun x => multiplierError α x * homotopyExp t 1 x -
        ∫ ς in (0 : ℝ)..1, (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x) :=
    funext (symbol_difference_eq_homotopy α t)
  have hAsm : ContDiff ℝ ∞ fun x => multiplierError α x * homotopyExp t 1 x :=
    (contDiff_multiplierError α).mul (contDiff_homotopyExp t 1)
  have hσsm : ContDiff ℝ ∞ fun x : ℝ =>
      diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
        (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ) := by
    have hl : ContDiff ℝ ∞ fun x => Real.exp (-t * laplacianSymbol x) := by
      unfold laplacianSymbol
      fun_prop
    have hg : ContDiff ℝ ∞ fun x : ℝ => Real.exp (-t * x ^ 2) := by
      fun_prop
    exact ((contDiff_diffMultiplier α).mul (ofRealCLM.contDiff.comp hl)).sub
      ((contDiff_imagMonomial α).mul (ofRealCLM.contDiff.comp hg))
  have hCsm : ContDiff ℝ ∞ fun x =>
      ∫ ς in (0 : ℝ)..1, (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x) := by
    have he : (fun x => ∫ ς in (0 : ℝ)..1,
          (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x)) =
        fun x => multiplierError α x * homotopyExp t 1 x -
          (diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
            (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) := by
      funext x
      rw [symbol_difference_eq_homotopy α t x]
      ring
    rw [he]
    exact hAsm.sub hσsm
  have hpt : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖iteratedDeriv n (fun x : ℝ =>
          diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
          (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ‖ₑ ≤
        ‖iteratedDeriv n (fun x => multiplierError α x * homotopyExp t 1 x) θ‖ₑ +
          ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
            binomialMoment n (diffOrder α + 4) *
            ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
              Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) := by
    intro θ hθ
    rw [hf, iteratedDeriv_fun_sub (hAsm.of_le (natCast_le_infty n)).contDiffAt
      (hCsm.of_le (natCast_le_infty n)).contDiffAt]
    refine (enorm_sub_le).trans ?_
    gcongr
    rw [iteratedDeriv_intervalIntegral_unit n
      (G := fun ς x => (t : ℂ) * (imagMonomialSymbolError α x * homotopyExp t ς x))
      (contDiff_homotopyIntegrand_prod α t) θ]
    exact enorm_intervalIntegral_unit_le fun ς hς =>
      enorm_iteratedDeriv_homotopyIntegrand_le hExp hProd hMono n α ht hς hθ
  have hfirst := (iteratedDeriv_mul_gaussian_bounds (n := n) (b := diffOrder α + 1) hProd hCsy ht
    (contDiff_multiplierError α) (contDiff_homotopyExp t 1)
    (fun κ _ θ hθ => (hMult α κ θ hθ).2)
    (fun κ _ θ hθ => enorm_iteratedDeriv_homotopyExp_le hExp ht (by simp) hθ κ)).2
  have hmeas : Measurable fun θ : ℝ => ENNReal.ofReal
      (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
        Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
    fun_prop
  have hsecond : ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
          binomialMoment n (diffOrder α + 4) *
          ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
            Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) ≤
      ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
          binomialMoment n (diffOrder α + 4) *
          ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) *
            t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2 - 1 / 2))) := by
    rw [lintegral_const_mul _ (hmeas.const_mul _), lintegral_const_mul _ hmeas,
      ← lintegral_rpow_mul_gaussian_half ht]
    gcongr
    exact Measure.restrict_le_self
  have hexp1 : ((n : ℝ) - (diffOrder α + 1 : ℕ) - 1) / 2 = ((n : ℝ) - diffOrder α - 2) / 2 := by
    push_cast
    ring
  have hpow : t * t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2 - 1 / 2) ≤
      t ^ (((n : ℝ) - diffOrder α - 2) / 2) := by
    nth_rewrite 1 [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    refine Real.rpow_le_rpow_of_exponent_le ht ?_
    push_cast
    linarith
  calc ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ‖iteratedDeriv n (fun x : ℝ =>
          diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) -
          (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ‖ₑ
      ≤ ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          (‖iteratedDeriv n (fun x => multiplierError α x * homotopyExp t 1 x) θ‖ₑ +
          ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
            binomialMoment n (diffOrder α + 4) *
            ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
              Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))))) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = (∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ‖iteratedDeriv n (fun x => multiplierError α x * homotopyExp t 1 x) θ‖ₑ) +
        ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant) *
            binomialMoment n (diffOrder α + 4) *
            ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2) *
              Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) :=
        lintegral_add_right _ ((hmeas.const_mul _).const_mul _)
    _ ≤ ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
          binomialMoment n (diffOrder α + 1) *
          ENNReal.ofReal (t ^ (((n : ℝ) - diffOrder α - 2) / 2)) +
        ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
          (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) * binomialMoment n (diffOrder α + 4)) *
          ENNReal.ofReal (t ^ (((n : ℝ) - diffOrder α - 2) / 2)) := by
        refine add_le_add ?_ (hsecond.trans ?_)
        · rw [← hexp1]
          exact hfirst
        · rw [ENNReal.ofReal_mul (p := 2 ^ (n + 1) * Real.pi ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := Real.pi ^ ((3 : ℝ) / 2)) (by positivity)]
          calc ENNReal.ofReal t * (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) *
                  ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α + 4) *
                  (ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) *
                    ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2 - 1 / 2))))
              = ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
                  (ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) *
                    binomialMoment n (diffOrder α + 4)) *
                  (ENNReal.ofReal t *
                    ENNReal.ofReal (t ^ (((n : ℝ) - (diffOrder α + 4 : ℕ)) / 2 - 1 / 2))) := by
                ring
            _ ≤ _ := by
                rw [← ENNReal.ofReal_mul ht0.le]
                gcongr
    _ = _ := by ring
end YangMills.Construction.FreeKernel.LatticeGaussianPeriod
end
