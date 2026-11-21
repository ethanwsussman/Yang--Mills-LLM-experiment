import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.BoundFromABoundAndADecay
import YangMills.Construction.FreeKernel.BoundOfTheDerivativesOfTheGaussianKernel
import YangMills.Construction.FreeKernel.LineIntegrationByParts
import YangMills.Construction.FreeKernel.MonomialGaussianDerivatives
import YangMills.Construction.FreeKernel.SymbolsAddUpAndKernelsAsFourierIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.GaussianDerivative
open Complex MeasureTheory YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
lemma gaussianHeatKernel_rescale {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    gaussianHeatKernel t ξ = (Real.sqrt t)⁻¹ * gaussianHeatKernel 1 ((Real.sqrt t)⁻¹ * ξ) := by
  have hq : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * Real.sqrt t :=
    Real.sqrt_mul (by positivity) t
  have hexp : -ξ ^ 2 / (4 * t) = -((Real.sqrt t)⁻¹ * ξ) ^ 2 / (4 * 1) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt ht.le]
    field_simp
  unfold gaussianHeatKernel
  rw [hq, hexp, mul_one, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring_nf
lemma contDiff_gaussianHeatKernel_one (k : ℕ) : ContDiff ℝ k (gaussianHeatKernel 1) := by
  unfold gaussianHeatKernel
  apply ContDiff.div_const
  apply Real.contDiff_exp.comp
  apply ContDiff.div_const
  exact (contDiff_id.pow 2).neg
lemma gaussianHeatKernelDeriv_rescale {t : ℝ} (ht : 0 < t) (k : ℕ) (ξ : ℝ) :
    gaussianHeatKernelDeriv k t ξ =
      (Real.sqrt t)⁻¹ * (((Real.sqrt t)⁻¹) ^ k *
        gaussianHeatKernelDeriv k 1 ((Real.sqrt t)⁻¹ * ξ)) := by
  have hfun : gaussianHeatKernel t =
      fun ξ => (Real.sqrt t)⁻¹ * gaussianHeatKernel 1 ((Real.sqrt t)⁻¹ * ξ) :=
    funext (gaussianHeatKernel_rescale ht)
  unfold gaussianHeatKernelDeriv
  rw [hfun, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (contDiff_gaussianHeatKernel_one k)]
lemma contDiff_monomial_mul_gaussian (b n : ℕ) :
    ContDiff ℝ n (fun θ : ℝ => (I * (θ : ℂ)) ^ b * (Real.exp (-1 * θ ^ 2) : ℂ)) := by
  apply ContDiff.mul
  · exact (contDiff_const.mul Complex.ofRealCLM.contDiff).pow b
  · exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.pow 2)))
lemma moment_le_sup (n m : ℕ) (hm : m = 0 ∨ m = n) (α : DiffKind) :
    ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * symmetryConstant) * binomialMoment m (diffOrder α) ≤
      ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b) := by
  have hb : diffOrder α ∈ ({0, 1, 2} : Finset ℕ) := by
    cases α <;> simp [diffOrder]
  have hF : ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * symmetryConstant) *
      binomialMoment m (diffOrder α) ≤ derivativeMoment m (diffOrder α) := by
    unfold derivativeMoment
    gcongr
    calc binomialMoment m (diffOrder α) ≤ 2 * binomialMoment m (diffOrder α) := by
          rw [two_mul]; exact le_self_add
      _ ≤ _ := by
          rw [add_assoc]; exact le_self_add
  refine hF.trans ?_
  refine le_trans ?_
    (Finset.le_sup (f := fun b => max (derivativeMoment 0 b) (derivativeMoment n b)) hb)
  rcases hm with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma bound_at_time_one
    (hFourier : FreeKernel.symbolsAndFourierIntegrals)
    (hMono : FreeKernel.MonomialGaussianDerivativeBounds)
    (hParts : FreeKernel.LineFourierIntegrationByParts)
    (hCombine : FreeKernel.BoundFromBoundAndDecay)
    (hNumbers : finite_and_pos)
    (n : ℕ) (α : DiffKind) (x : ℝ) :
    |gaussianHeatKernelDeriv (diffOrder α) 1 x| ≤
      (kernelDerivativeBound n).toReal *
        YangMills.Construction.FourDimKernel.bracketOnePlus |x| ^ (-(n : ℝ)) := by
  set σ : ℝ → ℂ := fun θ : ℝ => (I * (θ : ℂ)) ^ diffOrder α * (Real.exp (-1 * θ ^ 2) : ℂ)
    with hσ
  set E : ℕ → ENNReal := fun m =>
    ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * symmetryConstant) * binomialMoment m (diffOrder α)
    with hE
  have hpi : 0 < Real.pi ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hsym : 0 < symmetryConstant := by unfold symmetryConstant; positivity
  have hEtop : ∀ m, E m ≠ ⊤ := fun m =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNumbers.2.2.2.2.2.2.2.1 m (diffOrder α)).1
  have hint : ∀ (ξ : ℝ) (m : ℕ),
      ‖∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * iteratedDeriv m σ θ‖ ≤ (E m).toReal := by
    intro ξ m
    have h2 := (hMono α 1 le_rfl m).2.1
    have hen : ‖∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * iteratedDeriv m σ θ‖ₑ ≤ E m := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have hnorm : ∀ θ : ℝ, ‖Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * iteratedDeriv m σ θ‖ₑ =
          ‖iteratedDeriv m σ θ‖ₑ := by
        intro θ
        have he : ‖Complex.exp (I * (ξ : ℂ) * (θ : ℂ))‖ₑ = 1 := by
          have : I * (ξ : ℂ) * (θ : ℂ) = ((ξ * θ : ℝ) : ℂ) * I := by push_cast; ring
          rw [this, ← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
        rw [enorm_mul, he, one_mul]
      simp_rw [hnorm]
      refine h2.trans (le_of_eq ?_)
      rw [Real.one_rpow, ENNReal.ofReal_one, mul_one, hE]
      simp only
      rw [ENNReal.ofReal_mul hpi.le]
    have := ENNReal.toReal_mono (hEtop m) hen
    simpa [toReal_enorm] using this
  have hfour : ((gaussianHeatKernelDeriv (diffOrder α) 1 x : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ θ : ℝ, Complex.exp (I * (x : ℂ) * (θ : ℂ)) * σ θ := by
    rw [(hFourier.2 1 one_pos 0 x α).2.2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hσ]
    ring_nf
  have hnormfour : |gaussianHeatKernelDeriv (diffOrder α) 1 x| =
      1 / (2 * Real.pi) * ‖∫ θ : ℝ, Complex.exp (I * (x : ℂ) * (θ : ℂ)) * σ θ‖ := by
    have h := congrArg norm hfour
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul] at h
    rw [h]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have h2pi : 0 < 1 / (2 * Real.pi) := by positivity
  have hbound0 : |gaussianHeatKernelDeriv (diffOrder α) 1 x| ≤
      1 / (2 * Real.pi) * (E 0).toReal := by
    rw [hnormfour]
    refine mul_le_mul_of_nonneg_left ?_ h2pi.le
    simpa using hint x 0
  have hdecay : 0 < |x| → |gaussianHeatKernelDeriv (diffOrder α) 1 x| ≤
      1 / (2 * Real.pi) * (E n).toReal * |x| ^ (-(n : ℝ)) := by
    intro hx
    have hx0 : x ≠ 0 := abs_pos.1 hx
    have hpart := hParts n σ x hx0 (contDiff_monomial_mul_gaussian (diffOrder α) n) (fun k _ => by
      have h := hMono α 1 le_rfl k
      exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
    rw [hnormfour, hpart, norm_mul, norm_pow, norm_div, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, Real.rpow_neg (abs_nonneg x), Real.rpow_natCast, one_div_pow]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ h2pi.le
    rw [one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (hint x n) (by positivity)
  have hc := hCombine n |x| |gaussianHeatKernelDeriv (diffOrder α) 1 x|
    (1 / (2 * Real.pi) * (E 0).toReal) (1 / (2 * Real.pi) * (E n).toReal)
    (abs_nonneg x) (abs_nonneg _) (by positivity) (by positivity) hbound0 hdecay
  refine hc.trans ?_
  have hone : 0 < YangMills.Construction.FourDimKernel.bracketOnePlus |x| := by
    unfold YangMills.Construction.FourDimKernel.bracketOnePlus; positivity
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hone.le _)
  set S := ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b)
    with hS
  have hBtop := (hNumbers.2.2.2.2.2.2.2.2.2.1 n).1
  have hStop : S ≠ ⊤ := by
    intro h
    apply hBtop
    unfold kernelDerivativeBound
    rw [← hS, h]
    refine ENNReal.mul_top ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hB : (kernelDerivativeBound n).toReal = 2 ^ n / (2 * Real.pi) * S.toReal := by
    unfold kernelDerivativeBound
    rw [← hS, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hEle : ∀ m, (m = 0 ∨ m = n) → (E m).toReal ≤ S.toReal := fun m hm =>
    ENNReal.toReal_mono hStop (moment_le_sup n m hm α)
  rw [hB]
  have hmax : max (1 / (2 * Real.pi) * (E 0).toReal) (1 / (2 * Real.pi) * (E n).toReal) ≤
      1 / (2 * Real.pi) * S.toReal :=
    max_le (mul_le_mul_of_nonneg_left (hEle 0 (Or.inl rfl)) h2pi.le)
      (mul_le_mul_of_nonneg_left (hEle n (Or.inr rfl)) h2pi.le)
  calc (2 : ℝ) ^ n * max _ _ ≤ 2 ^ n * (1 / (2 * Real.pi) * S.toReal) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = 2 ^ n / (2 * Real.pi) * S.toReal := by ring
theorem gaussianDerivativeBound_holds
    (hFourier : FreeKernel.symbolsAndFourierIntegrals)
    (hMono : FreeKernel.MonomialGaussianDerivativeBounds)
    (hParts : FreeKernel.LineFourierIntegrationByParts)
    (hCombine : FreeKernel.BoundFromBoundAndDecay)
    (hNumbers : finite_and_pos) :
    FreeKernel.GaussianDerivativeBound := by
  intro n α t ht ξ
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hone := bound_at_time_one hFourier hMono hParts hCombine hNumbers n α ((Real.sqrt t)⁻¹ * ξ)
  have hx : |(Real.sqrt t)⁻¹ * ξ| = |ξ| / Real.sqrt t := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hs), div_eq_inv_mul]
  rw [hx] at hone
  have hpow : (Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹) ^ diffOrder α =
      t ^ (-(((diffOrder α : ℝ) + 1) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← pow_succ', ← Real.rpow_neg_one, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring_nf
  rw [gaussianHeatKernelDeriv_rescale ht, ← mul_assoc, hpow, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  calc t ^ (-(((diffOrder α : ℝ) + 1) / 2)) * _ ≤ t ^ (-(((diffOrder α : ℝ) + 1) / 2)) * _ :=
        mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg ht.le _)
    _ = _ := by ring_nf
end YangMills.Construction.FreeKernel.GaussianDerivative
end
