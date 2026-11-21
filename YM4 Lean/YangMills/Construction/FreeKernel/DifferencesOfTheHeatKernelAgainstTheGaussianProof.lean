import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.BoundFromABoundAndADecay
import YangMills.Construction.FreeKernel.DifferencesOfTheHeatKernelAgainstTheGaussian
import YangMills.Construction.FreeKernel.LatticeGaussianPeriodDifference
import YangMills.Construction.FreeKernel.LineIntegrationByParts
import YangMills.Construction.FreeKernel.MonomialGaussianDerivatives
import YangMills.Construction.FreeKernel.MonomialGaussianTail
import YangMills.Construction.FreeKernel.PeriodicIntegrationByParts
import YangMills.Construction.FreeKernel.SymbolsAddUpAndKernelsAsFourierIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatKernelGaussian
open Complex MeasureTheory Filter Topology LatticeKernel Constants.HeatKernel FourDimKernel
theorem enorm_cexp_phase_mul (j : ℤ) (θ : ℝ) (z : ℂ) :
    ‖Complex.exp (I * (j : ℂ) * (θ : ℂ)) * z‖ₑ = ‖z‖ₑ := by
  have h : ‖Complex.exp (I * (j : ℂ) * (θ : ℂ))‖ = 1 := by
    have : I * (j : ℂ) * (θ : ℂ) = (((j : ℝ) * θ : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [← ofReal_norm, ← ofReal_norm, norm_mul, h, one_mul]
theorem compl_Icc_neg_pi_pi : (Set.Icc (-Real.pi) Real.pi)ᶜ = {θ : ℝ | Real.pi < |θ|} := by
  ext θ
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, ← abs_le, not_le]
theorem enorm_period_sub_line_le (σL σG : ℝ → ℂ) (m : ℕ) (hL : ContDiff ℝ m σL)
    (hG : ContDiff ℝ m σG) (hint : Integrable (iteratedDeriv m σG)) (j : ℤ) :
    ‖(∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv m σL θ) -
        ∫ θ : ℝ, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv m σG θ‖ₑ ≤
      (∫⁻ θ in Set.Icc (-Real.pi) Real.pi, ‖iteratedDeriv m (fun x => σL x - σG x) θ‖ₑ) +
        ∫⁻ θ in {θ : ℝ | Real.pi < |θ|}, ‖iteratedDeriv m σG θ‖ₑ := by
  have hcL : Continuous (iteratedDeriv m σL) := hL.continuous_iteratedDeriv m le_rfl
  have hcG : Continuous (iteratedDeriv m σG) := hG.continuous_iteratedDeriv m le_rfl
  have hph : Continuous fun θ : ℝ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) := by fun_prop
  set f : ℝ → ℂ := fun θ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv m σL θ with hf
  set g : ℝ → ℂ := fun θ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv m σG θ with hg
  have hfc : Continuous f := hph.mul hcL
  have hgc : Continuous g := hph.mul hcG
  have hgi : Integrable g := by
    refine hint.mono hgc.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    have : ‖g θ‖ₑ = ‖iteratedDeriv m σG θ‖ₑ := enorm_cexp_phase_mul j θ _
    rw [← ofReal_norm, ← ofReal_norm] at this
    exact le_of_eq ((ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (norm_nonneg _)).1 this)
  have hmeas : MeasurableSet (Set.Icc (-Real.pi) Real.pi) := measurableSet_Icc
  have hsplit := integral_add_compl hmeas hgi
  rw [compl_Icc_neg_pi_pi] at hsplit
  have hper : ∫ θ in (-Real.pi)..Real.pi, f θ = ∫ θ in Set.Icc (-Real.pi) Real.pi, f θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]
  have hfi : IntegrableOn f (Set.Icc (-Real.pi) Real.pi) := hfc.continuousOn.integrableOn_Icc
  have hgi' : IntegrableOn g (Set.Icc (-Real.pi) Real.pi) := hgc.continuousOn.integrableOn_Icc
  have hdiff : ∀ θ : ℝ, f θ - g θ = Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
      iteratedDeriv m (fun x => σL x - σG x) θ := by
    intro θ
    have : iteratedDeriv m (fun x => σL x - σG x) θ =
        iteratedDeriv m σL θ - iteratedDeriv m σG θ :=
      iteratedDeriv_sub hL.contDiffAt hG.contDiffAt
    rw [this, hf, hg]; ring
  have hrw : (∫ θ in (-Real.pi)..Real.pi, f θ) - ∫ θ : ℝ, g θ =
      (∫ θ in Set.Icc (-Real.pi) Real.pi, (f θ - g θ)) - ∫ θ in {θ : ℝ | Real.pi < |θ|}, g θ := by
    rw [hper, integral_sub hfi hgi', ← hsplit]; ring
  rw [hrw]
  refine (enorm_sub_le).trans (add_le_add ?_ ?_)
  · refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun θ => ?_
    rw [hdiff, enorm_cexp_phase_mul]
  · refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun θ => ?_
    exact enorm_cexp_phase_mul j θ _
theorem contDiff_latticeIntegrand (α : DiffKind) (t : ℝ) (m : ℕ) :
    ContDiff ℝ m (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) := by
  have hs : ContDiff ℝ m laplacianSymbol := by
    unfold laplacianSymbol
    exact contDiff_const.sub (contDiff_const.mul Real.contDiff_cos)
  have hc : ContDiff ℝ m (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have he : ContDiff ℝ m (fun x : ℝ => (Real.exp (-t * laplacianSymbol x) : ℂ)) :=
    hc.comp (contDiff_const.mul hs).exp
  refine ContDiff.mul ?_ he
  cases α with
  | identity => exact contDiff_const
  | forward => exact ((contDiff_const.mul hc).cexp).sub contDiff_const
  | backward => exact contDiff_const.sub ((contDiff_const.mul hc).neg.cexp)
  | laplacian => exact (hc.comp hs).neg
theorem contDiff_gaussianIntegrand (α : DiffKind) (t : ℝ) (m : ℕ) :
    ContDiff ℝ m (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) := by
  have hc : ContDiff ℝ m (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have he : ContDiff ℝ m (fun x : ℝ => (Real.exp (-t * x ^ 2) : ℂ)) :=
    hc.comp (contDiff_const.mul (contDiff_id.pow 2)).exp
  exact ((contDiff_const.mul hc).pow _).mul he
theorem periodic_latticeIntegrand (α : DiffKind) (t : ℝ) :
    Function.Periodic
      (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ))
      (2 * Real.pi) := by
  have hs : ∀ x : ℝ, laplacianSymbol (x + 2 * Real.pi) = laplacianSymbol x := by
    intro x; simp [laplacianSymbol, Real.cos_add_two_pi]
  have hp : ∀ x : ℝ, Complex.exp (I * ((x + 2 * Real.pi : ℝ) : ℂ)) = Complex.exp (I * (x : ℂ)) := by
    intro x
    have : I * ((x + 2 * Real.pi : ℝ) : ℂ) = I * (x : ℂ) + 2 * (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.exp_periodic]
  have hm : ∀ x : ℝ, Complex.exp (-(I * ((x + 2 * Real.pi : ℝ) : ℂ))) =
      Complex.exp (-(I * (x : ℂ))) := by
    intro x
    rw [Complex.exp_neg, Complex.exp_neg, hp]
  intro x
  show diffMultiplier α (x + 2 * Real.pi) *
      (Real.exp (-t * laplacianSymbol (x + 2 * Real.pi)) : ℂ) =
    diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)
  rw [hs]
  congr 1
  cases α with
  | identity => rfl
  | forward => simp only [diffMultiplier]; rw [hp]
  | backward => simp only [diffMultiplier]; rw [hm]
  | laplacian => simp only [diffMultiplier]; rw [hs]
theorem norm_period_sub_line_le
    (hfinite : Constants.HeatKernel.finite_and_pos)
    (hmono : MonomialGaussianDerivativeBounds)
    (htail : MonomialGaussianTailBound)
    (hperiod : LatticeGaussianDifferenceOnPeriod)
    (m : ℕ) (α : DiffKind) (t : ℝ) (ht : 1 ≤ t) (j : ℤ) :
    ‖(∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
          iteratedDeriv m
            (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) θ) -
        ∫ θ : ℝ, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
          iteratedDeriv m
            (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ‖ ≤
      (derivativeMoment m (diffOrder α)).toReal * t ^ (((m : ℝ) - diffOrder α - 2) / 2) := by
  have hint := (hmono α t ht m).2.2.1
  have h1 := enorm_period_sub_line_le _ _ m (contDiff_latticeIntegrand α t m)
    (contDiff_gaussianIntegrand α t m) hint j
  have h2 := hperiod m α t ht
  have h3 := htail m α t ht
  have hτ : 0 ≤ t ^ (((m : ℝ) - diffOrder α - 2) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hpi : 0 ≤ Real.pi ^ ((3 : ℝ) / 2) := Real.rpow_nonneg Real.pi_pos.le _
  have hC : 0 ≤ symmetryConstant := by unfold symmetryConstant; positivity
  have hsum : ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
        (binomialMoment m (diffOrder α + 1) +
          ENNReal.ofReal (2 ^ (m + 1) * Real.pi ^ 2) * binomialMoment m (diffOrder α + 4)) *
        ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 2) / 2)) +
      ENNReal.ofReal (2 * Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
        binomialMoment m (diffOrder α) *
        ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 2) / 2)) =
      derivativeMoment m (diffOrder α) *
        ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 2) / 2)) := by
    unfold derivativeMoment
    rw [ENNReal.ofReal_mul hpi, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat]
    ring
  have hle := h1.trans ((add_le_add h2 h3).trans (le_of_eq hsum))
  have hfin : derivativeMoment m (diffOrder α) *
      ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 2) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (hfinite.2.2.2.2.2.2.2.2.1 m (diffOrder α)).1 ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin hle
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ] at this
theorem norm_kernel_sub_gaussian_le_of_factor
    (hfourier : symbolsAndFourierIntegrals)
    (hfinite : Constants.HeatKernel.finite_and_pos)
    (hmono : MonomialGaussianDerivativeBounds)
    (htail : MonomialGaussianTailBound)
    (hperiod : LatticeGaussianDifferenceOnPeriod)
    (m : ℕ) (α : DiffKind) (t : ℝ) (ht : 1 ≤ t) (j : ℤ) (c : ℂ)
    (hcL : ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) θ =
      c * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        iteratedDeriv m
          (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) θ)
    (hcG : ∫ θ : ℝ, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ =
      c * ∫ θ : ℝ, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        iteratedDeriv m
          (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ) :
    ‖diffOp α (discreteHeatKernel t) j -
        ((gaussianHeatKernelDeriv (diffOrder α) t (j : ℝ) : ℝ) : ℂ)‖ ≤
      ‖c‖ / (2 * Real.pi) *
        ((derivativeMoment m (diffOrder α)).toReal * t ^ (((m : ℝ) - diffOrder α - 2) / 2)) := by
  obtain ⟨-, hq, hg⟩ := hfourier.2 t (by linarith) j (j : ℝ) α
  have hb := norm_period_sub_line_le hfinite hmono htail hperiod m α t ht j
  simp only [Complex.ofReal_intCast] at hg
  have hq' : diffOp α (discreteHeatKernel t) j = (1 / (2 * (Real.pi : ℂ))) *
      ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) θ := by
    rw [hq]; simp only [mul_assoc]
  have hg' : ((gaussianHeatKernelDeriv (diffOrder α) t (j : ℝ) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ θ : ℝ, Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
        (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α * (Real.exp (-t * x ^ 2) : ℂ)) θ := by
    rw [hg]; simp only [mul_assoc]
  rw [hq', hg', hcL, hcG, ← mul_sub, ← mul_sub, norm_mul, norm_mul]
  have hpi : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  rw [hpi]
  have h2pi : 0 < 2 * Real.pi := by positivity
  calc 1 / (2 * Real.pi) * (‖c‖ * _) ≤
      1 / (2 * Real.pi) * (‖c‖ * ((derivativeMoment m (diffOrder α)).toReal *
        t ^ (((m : ℝ) - diffOrder α - 2) / 2))) := by gcongr
    _ = _ := by ring
theorem heatKernelGaussianDifferenceBound_holds
    (hfourier : symbolsAndFourierIntegrals)
    (hfinite : Constants.HeatKernel.finite_and_pos)
    (hmono : MonomialGaussianDerivativeBounds)
    (htail : MonomialGaussianTailBound)
    (hperiod : LatticeGaussianDifferenceOnPeriod)
    (hpartsPeriod : PeriodicFourierIntegrationByParts)
    (hpartsLine : LineFourierIntegrationByParts)
    (hcombine : BoundFromBoundAndDecay) :
    HeatKernelGaussianDifferenceBound := by
  intro n α t ht j
  have ht0 : 0 < t := by linarith
  set b : ℕ := diffOrder α with hbdef
  set B₁ : ℝ := t ^ (-(((b : ℝ) + 2) / 2)) with hB₁
  have hB₁0 : 0 ≤ B₁ := Real.rpow_nonneg ht0.le _
  set y : ℝ := |(j : ℝ)| / Real.sqrt t with hy
  have hy0 : 0 ≤ y := div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set F₀ : ℝ := (derivativeMoment 0 b).toReal with hF₀
  set Fₙ : ℝ := (derivativeMoment n b).toReal with hFₙ
  have hF₀0 : 0 ≤ F₀ := ENNReal.toReal_nonneg
  have hFₙ0 : 0 ≤ Fₙ := ENNReal.toReal_nonneg
  have hzero : ‖diffOp α (discreteHeatKernel t) j -
      ((gaussianHeatKernelDeriv (diffOrder α) t (j : ℝ) : ℝ) : ℂ)‖ ≤ F₀ / (2 * Real.pi) * B₁ := by
    have h := norm_kernel_sub_gaussian_le_of_factor hfourier hfinite hmono htail hperiod
      0 α t ht j 1 (by simp) (by simp)
    have he : (((0 : ℕ) : ℝ) - (diffOrder α : ℝ) - 2) / 2 = -(((b : ℝ) + 2) / 2) := by
      rw [hbdef]; push_cast; ring
    rw [he, norm_one] at h
    refine h.trans (le_of_eq ?_)
    rw [hB₁, hF₀]; ring
  have hdecay : 0 < y → ‖diffOp α (discreteHeatKernel t) j -
      ((gaussianHeatKernelDeriv (diffOrder α) t (j : ℝ) : ℝ) : ℂ)‖ ≤
      Fₙ / (2 * Real.pi) * B₁ * y ^ (-(n : ℝ)) := by
    intro hypos
    have hj : j ≠ 0 := by
      rintro rfl
      simp [hy] at hypos
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    have hL := hpartsPeriod n _ j hj (contDiff_latticeIntegrand α t n)
      (periodic_latticeIntegrand α t)
    have hG := hpartsLine n _ (j : ℝ) hjR (contDiff_gaussianIntegrand α t n)
      (fun κ _ => ⟨(hmono α t ht κ).2.2.1, (hmono α t ht κ).2.2.2.1, (hmono α t ht κ).2.2.2.2⟩)
    simp only [Complex.ofReal_intCast] at hG
    have h := norm_kernel_sub_gaussian_le_of_factor hfourier hfinite hmono htail hperiod
      n α t ht j ((I / (j : ℂ)) ^ n) hL hG
    refine h.trans (le_of_eq ?_)
    have hc : ‖(I / (j : ℂ)) ^ n‖ = (|(j : ℝ)| ^ n)⁻¹ := by
      rw [norm_pow, norm_div, Complex.norm_I, Complex.norm_intCast, one_div, inv_pow]
    have hyn : y ^ (-(n : ℝ)) = t ^ ((n : ℝ) / 2) * (|(j : ℝ)| ^ n)⁻¹ := by
      rw [Real.rpow_neg hy0, Real.rpow_natCast, hy, div_pow, inv_div, div_eq_mul_inv]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 1
      ring
    have hte : t ^ (((n : ℝ) - (diffOrder α : ℝ) - 2) / 2) = B₁ * t ^ ((n : ℝ) / 2) := by
      rw [hB₁, ← Real.rpow_add ht0, hbdef]
      congr 1
      ring
    rw [hc, hyn, hte, hFₙ, hbdef]
    ring
  have hX := hcombine n y _ (F₀ / (2 * Real.pi) * B₁) (Fₙ / (2 * Real.pi) * B₁) hy0
    (norm_nonneg _) (by positivity) (by positivity) hzero hdecay
  set S : ENNReal :=
    ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b) with hS
  have hcoef : 0 < 2 ^ n / (2 * Real.pi) := by positivity
  have hSfin : S ≠ ⊤ := by
    intro hStop
    have hB := (hfinite.2.2.2.2.2.2.2.2.2.1 n).1
    apply hB
    unfold kernelDerivativeBound
    rw [← hS, hStop]
    exact ENNReal.mul_top (by simpa using hcoef)
  have hbmem : b ∈ ({0, 1, 2} : Finset ℕ) := by
    rw [hbdef]; cases α <;> simp [diffOrder]
  have hleS : max (derivativeMoment 0 b) (derivativeMoment n b) ≤ S :=
    Finset.le_sup (f := fun b => max (derivativeMoment 0 b) (derivativeMoment n b)) hbmem
  have hF₀S : F₀ ≤ S.toReal := ENNReal.toReal_mono hSfin ((le_max_left _ _).trans hleS)
  have hFₙS : Fₙ ≤ S.toReal := ENNReal.toReal_mono hSfin ((le_max_right _ _).trans hleS)
  have hBn : (kernelDerivativeBound n).toReal = 2 ^ n / (2 * Real.pi) * S.toReal := by
    unfold kernelDerivativeBound
    rw [← hS, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef.le]
  have hmax : max (F₀ / (2 * Real.pi) * B₁) (Fₙ / (2 * Real.pi) * B₁) ≤
      S.toReal / (2 * Real.pi) * B₁ := by
    apply max_le <;> gcongr
  have hone : 0 ≤ bracketOnePlus y ^ (-(n : ℝ)) := by
    refine Real.rpow_nonneg ?_ _
    unfold bracketOnePlus; linarith
  refine hX.trans ?_
  calc (2 : ℝ) ^ n * max (F₀ / (2 * Real.pi) * B₁) (Fₙ / (2 * Real.pi) * B₁) *
        bracketOnePlus y ^ (-(n : ℝ)) ≤
      2 ^ n * (S.toReal / (2 * Real.pi) * B₁) * bracketOnePlus y ^ (-(n : ℝ)) := by gcongr
    _ = (kernelDerivativeBound n).toReal * B₁ * bracketOnePlus y ^ (-(n : ℝ)) := by
      rw [hBn]; ring
end YangMills.Construction.FreeKernel.HeatKernelGaussian
end
