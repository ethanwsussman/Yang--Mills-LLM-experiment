import YangMills.Construction.Continuum.CutoffOfTheParametrix
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.Parametrix
open TorusMetric
theorem shellCutoff_spec : shellCutoff_properties := by
  have hstep : smoothStep = expNegInvGlue := by
    funext t
    by_cases ht : 0 < t
    · simp [smoothStep, expNegInvGlue, ht, not_le.2 ht, neg_div, one_div]
    · simp [smoothStep, expNegInvGlue, ht, not_lt.1 ht]
  have hsq : ∀ x, euclidNormVec x ^ 2 = ∑ μ, x μ ^ 2 := fun x =>
    Real.sq_sqrt (Finset.sum_nonneg fun μ _ => sq_nonneg _)
  have hpos : ∀ t : ℝ,
      0 < expNegInvGlue (2 - 4 * t) + expNegInvGlue (4 * t - 1) := by
    intro t
    by_cases h : 0 < 2 - 4 * t
    · exact add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos h)
        (expNegInvGlue.nonneg _)
    · exact add_pos_of_nonneg_of_pos (expNegInvGlue.nonneg _)
        (expNegInvGlue.pos_of_pos (by linarith))
  have hformula : ∀ x, shellCutoff x = expNegInvGlue (2 - 4 * euclidNormVec x ^ 2) /
      (expNegInvGlue (2 - 4 * euclidNormVec x ^ 2) +
        expNegInvGlue (4 * euclidNormVec x ^ 2 - 1)) := by
    intro x
    simp only [shellCutoff, hstep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => ∑ μ, x μ ^ 2) :=
      ContDiff.sum fun μ _ => (contDiff_apply ℝ ℝ μ).pow 2
    have hnum : ContDiff ℝ ∞
        (fun x : Fin 4 → ℝ => expNegInvGlue (2 - 4 * ∑ μ, x μ ^ 2)) :=
      expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_const.mul hr))
    have hother : ContDiff ℝ ∞
        (fun x : Fin 4 → ℝ => expNegInvGlue (4 * (∑ μ, x μ ^ 2) - 1)) :=
      expNegInvGlue.contDiff.comp ((contDiff_const.mul hr).sub contDiff_const)
    have heq : shellCutoff = fun x : Fin 4 → ℝ =>
        expNegInvGlue (2 - 4 * ∑ μ, x μ ^ 2) /
          (expNegInvGlue (2 - 4 * ∑ μ, x μ ^ 2) +
            expNegInvGlue (4 * (∑ μ, x μ ^ 2) - 1)) := by
      funext x
      rw [hformula, hsq]
    rw [heq]
    exact hnum.div (hnum.add hother) fun x => (hpos _).ne'
  · intro x
    rw [hformula]
    have hd := hpos (euclidNormVec x ^ 2)
    constructor
    · exact div_nonneg (expNegInvGlue.nonneg _) hd.le
    · rw [div_le_one hd]
      exact le_add_of_nonneg_right (expNegInvGlue.nonneg _)
  · intro x hx
    have h0 : 0 ≤ euclidNormVec x := Real.sqrt_nonneg _
    have hle : euclidNormVec x ^ 2 ≤ 1 / 4 := by nlinarith
    rw [hformula, expNegInvGlue.zero_of_nonpos (x := 4 * euclidNormVec x ^ 2 - 1) (by linarith),
      add_zero]
    exact div_self (expNegInvGlue.pos_of_pos (by linarith)).ne'
  · intro x hx
    rw [hformula, expNegInvGlue.zero_of_nonpos (x := 2 - 4 * euclidNormVec x ^ 2) (by linarith),
      zero_div]
end YangMills.Construction.Parametrix
