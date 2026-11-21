import YangMills.Construction.FreeKernel.MonomialGaussianDerivatives
import YangMills.Construction.FreeKernel.MonomialGaussianTail
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex MeasureTheory YangMills.Construction.LatticeKernel
open YangMills.Construction.Constants.HeatKernel
namespace GaussianTail
theorem exp_neg_half_heatDecay_le (t θ : ℝ) (ht : 1 ≤ t) (hθ : Real.pi < |θ|) :
    Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)) ≤
      Real.exp (-t / 2) * Real.exp (-(t / (2 * Real.pi ^ 2)) * θ ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : Real.pi ^ 2 ≤ θ ^ 2 := by
    apply le_of_lt
    apply sq_lt_sq.mpr
    rwa [abs_of_pos hpi]
  have hu : 1 ≤ θ ^ 2 / Real.pi ^ 2 := (one_le_div (by positivity)).mpr hsq
  have e1 : 1 / 2 * heatDecay * t * θ ^ 2 = t * (θ ^ 2 / Real.pi ^ 2) := by
    unfold heatDecay
    field_simp
  have e2 : t / (2 * Real.pi ^ 2) * θ ^ 2 = t * (θ ^ 2 / Real.pi ^ 2) / 2 := by
    field_simp
  rw [← Real.exp_add, Real.exp_le_exp, e1, neg_mul, e2]
  nlinarith
theorem rpow_mul_exp_mul_sqrt_le (t a : ℝ) (ht : 1 ≤ t) :
    t ^ a * Real.exp (-t / 2) * Real.sqrt (Real.pi / (t / (2 * Real.pi ^ 2))) ≤
      2 * Real.pi ^ ((3 : ℝ) / 2) * t ^ (a - 1) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 < t := by linarith
  set K : ℝ := Real.pi ^ ((3 : ℝ) / 2) with hK
  have hK2 : K ^ 2 = Real.pi ^ 3 := by
    rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hpi.le, ← Real.rpow_natCast]
    norm_num
  set E : ℝ := Real.exp (t / 2) with hE
  have hE2 : E ^ 2 = Real.exp t := by
    rw [hE, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : Real.exp (-t / 2) * E = 1 := by
    rw [hE, ← Real.exp_add]
    simp [neg_div]
  have hexp : t ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  have hs : Real.sqrt (Real.pi / (t / (2 * Real.pi ^ 2))) ≤ 2 * K * E / t := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : Real.pi / (t / (2 * Real.pi ^ 2)) = 2 * Real.pi ^ 3 / t := by
      field_simp
    have e' : (2 * K * E / t) ^ 2 = 4 * Real.pi ^ 3 * Real.exp t / t ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, hK2, hE2]
      ring
    rw [e, e', div_le_div_iff₀ ht0 (by positivity)]
    have hp3 : 0 < Real.pi ^ 3 := by positivity
    have h1 : t * t ≤ Real.exp t * t := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left h1 hp3.le, mul_pos hp3 (mul_pos ht0 ht0)]
  calc t ^ a * Real.exp (-t / 2) * Real.sqrt (Real.pi / (t / (2 * Real.pi ^ 2)))
      ≤ t ^ a * Real.exp (-t / 2) * (2 * K * E / t) := by gcongr
    _ = 2 * K * (t ^ a / t) * (Real.exp (-t / 2) * E) := by ring
    _ = 2 * K * t ^ (a - 1) := by
      rw [hinv, Real.rpow_sub_one ht0.ne', mul_one]
end GaussianTail
open GaussianTail in
theorem monomialGaussianTailBound (hD : MonomialGaussianDerivativeBounds) :
    MonomialGaussianTailBound := by
  intro n α t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hpt, -⟩ := hD α t ht n
  set a : ℝ := ((n : ℝ) - diffOrder α) / 2 with ha
  set β : ℝ := t / (2 * Real.pi ^ 2) with hβdef
  have hβ : 0 < β := by positivity
  set Y : ℝ → ℝ := fun θ => t ^ a * Real.exp (-t / 2) * Real.exp (-β * θ ^ 2) with hY
  have hS : MeasurableSet {θ : ℝ | Real.pi < |θ|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hYint : Integrable Y := (integrable_exp_neg_mul_sq hβ).const_mul _
  have hYnn : 0 ≤ᵐ[volume] Y := Filter.Eventually.of_forall fun θ => by
    have : 0 < t ^ a := Real.rpow_pos_of_pos ht0 _
    simp only [hY, Pi.zero_apply]
    positivity
  have hYval : ∫ θ, Y θ = t ^ a * Real.exp (-t / 2) * Real.sqrt (Real.pi / β) := by
    simp only [hY]
    rw [integral_const_mul, integral_gaussian]
  have hYmeas : Measurable fun θ => ENNReal.ofReal (Y θ) := by
    apply ENNReal.measurable_ofReal.comp
    simp only [hY]
    fun_prop
  have hexpo : ((n : ℝ) - diffOrder α - 2) / 2 = a - 1 := by
    rw [ha]
    ring
  calc ∫⁻ θ in {θ : ℝ | Real.pi < |θ|},
        ‖iteratedDeriv n (fun θ : ℝ => (I * (θ : ℂ)) ^ diffOrder α * (Real.exp (-t * θ ^ 2) : ℂ)) θ‖ₑ
      ≤ ∫⁻ θ in {θ : ℝ | Real.pi < |θ|},
          ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α) * ENNReal.ofReal (Y θ) := by
        refine setLIntegral_mono' hS fun θ hθ => (hpt θ).trans ?_
        gcongr
        have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht0 _
        have := exp_neg_half_heatDecay_le t θ ht hθ
        simp only [hY]
        rw [mul_assoc (t ^ a) (Real.exp (-t / 2))]
        exact mul_le_mul_of_nonneg_left this hta.le
    _ ≤ ∫⁻ θ, ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α) *
          ENNReal.ofReal (Y θ) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α) *
          ∫⁻ θ, ENNReal.ofReal (Y θ) :=
        lintegral_const_mul _ hYmeas
    _ = ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α) *
          ENNReal.ofReal (∫ θ, Y θ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hYint hYnn]
    _ ≤ ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder α) *
          ENNReal.ofReal (2 * Real.pi ^ ((3 : ℝ) / 2) * t ^ (a - 1)) := by
        gcongr
        rw [hYval]
        exact rpow_mul_exp_mul_sqrt_le t a ht
    _ = ENNReal.ofReal (2 * Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
          binomialMoment n (diffOrder α) * ENNReal.ofReal (t ^ (((n : ℝ) - diffOrder α - 2) / 2)) := by
        rw [hexpo, ENNReal.ofReal_mul (by positivity)]
        ring
end YangMills.Construction.FreeKernel
end
