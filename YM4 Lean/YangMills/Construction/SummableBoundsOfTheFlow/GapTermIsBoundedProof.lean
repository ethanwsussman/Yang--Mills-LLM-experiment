import YangMills.Construction.ClusterExpansionOfAStep.GroupGapIsSmoothForm
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponentProof
import YangMills.Construction.SummableBoundsOfTheFlow.GapTermIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SummableBounds
open BlockAverages ColdStepAtMirrorFrames
namespace HaarGapExcess
variable {F : BlockFrame}
theorem contourAverage_norm_bounds (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (hdef : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c h π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖contourAverage W c‖ ∧ ‖contourAverage W c‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.norm_contourAverage_mem_shell <;> assumption
theorem haarGap_scale_sub {C₁ s r : ℝ} (hd : Differentiable ℝ haarGap)
    (hC : ∀ u : ℝ, 1 ≤ u → |u * deriv haarGap u| ≤ C₁) (hs : 2 ≤ s) (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) :
    |haarGap (s * r) - haarGap s| ≤ C₁ := by
  have hsr : 1 ≤ s * r := by nlinarith
  have hsr0 : 0 < s * r := by linarith
  have hC0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC 1 le_rfl)
  have hb : ∀ u ∈ Set.Icc (s * r) s, ‖deriv haarGap u‖ ≤ C₁ / (s * r) := by
    intro u hu
    have hu1 : 1 ≤ u := hsr.trans hu.1
    have h1 := hC u hu1
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < u)] at h1
    rw [Real.norm_eq_abs, le_div_iff₀ hsr0]
    have h2 : s * r * |deriv haarGap u| ≤ u * |deriv haarGap u| :=
      mul_le_mul_of_nonneg_right hu.1 (abs_nonneg _)
    linarith
  have hmem : s * r ≤ s := by nlinarith
  have := (convex_Icc (s * r) s).norm_image_sub_le_of_norm_deriv_le (fun u _ => hd u) hb
    (Set.left_mem_Icc.2 hmem) (Set.right_mem_Icc.2 hmem)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - s * r)] at this
  rw [abs_sub_comm]
  refine this.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hsr0]
  have h3 : s - s * r ≤ s * r := by nlinarith
  exact mul_le_mul_of_nonneg_left h3 hC0
end HaarGapExcess
open HaarGapExcess in
theorem haarGapExcessBounded (hD : HaarGapDerivBound) (hS : HaarGapSmoothStatement) :
    ScaledVariables.HaarGapExcessBounded := by
  obtain ⟨C₁, hC⟩ := hD 1 le_rfl
  have hd : Differentiable ℝ haarGap := hS.differentiable (by simp)
  have hC' : ∀ u : ℝ, 1 ≤ u → |u * deriv haarGap u| ≤ C₁ := by
    intro u hu
    have := hC u hu
    simpa [iteratedDeriv_one] using this
  refine ⟨C₁, (abs_nonneg _).trans (hC' 1 le_rfl), fun F a x W V c hL ha hx h => ?_⟩
  obtain ⟨h1, h2⟩ := contourAverage_norm_bounds hL W V c h
  exact haarGap_scale_sub hd hC' (by nlinarith) h1 h2
end YangMills.Construction.SummableBounds
end
