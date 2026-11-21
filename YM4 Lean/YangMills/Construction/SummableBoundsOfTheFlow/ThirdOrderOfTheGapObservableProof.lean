import YangMills.Construction.SummableBoundsOfTheFlow.GapObservableHasTheConditionsOfThirdOrder
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersHaveACouplingAboveOne
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftExists
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderOfTheGapObservableForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
theorem gapObservableThirdOrder_of_bounds
    (hJoin : SummableBounds.joinAtLoweredConstantsStatement)
    (hOne : SummableBounds.couplingAtLeastOneStatement) (hShift : rightTranslationDerivExistsStatement)
    (hCov : thirdOrderCovarianceBound) (hHyp : gapObservableThirdOrderStatement) :
    gapObservableThirdOrderBound := by
  obtain ⟨Th, hTh⟩ := hShift
  refine hJoin _ _ gapObservableThirdOrderBoundAt (fun _ => 1) (fun _ => 0) hCov (hOne _ hHyp) ?_
  intro T c c' hc hc' hodd hn hE hη hη1 hG _ hTO hCl N
  obtain ⟨hCl, hy⟩ := hCl
  obtain ⟨CN, Cq, hCN, hCq, hcl⟩ := hCl N
  have hCs : T.Cs ≠ 0 := by
    have : (0 : ℝ) < T.Cs := by linarith
    exact this.ne'
  have hCU : 0 ≤ 1 + ∑ q ∈ Finset.range 7, Cq q := by
    have : 0 ≤ ∑ q ∈ Finset.range 7, Cq q := Finset.sum_nonneg fun q _ => hCq q
    linarith
  have hE₃ : 0 ≤ T.E / T.η₃ := by
    have : 0 ≤ T.E := by linarith
    positivity
  refine ⟨2 * (c * (1 + ∑ q ∈ Finset.range 7, Cq q) * (T.E / T.η₃) * CN * c / T.Cs), ?_⟩
  intro t x s φ F V Y c₃ X hx hs hs1 hφ hTF hV hX hside
  have hx1 : 1 ≤ x := hy.trans hx
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have cl := hcl t x s φ F V Y c₃ X Th hx hs hs1 hφ hTF hV hX hside hTh
  obtain ⟨α, hαd⟩ : ∃ α, α = CN * (x ^ N)⁻¹ * (c * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))) := ⟨_, rfl⟩
  have hα : 0 < α := by
    rw [hαd]
    positivity
  rw [← hαd] at cl
  have b := hTO Cq hCq t x s α α φ φ F V Y c₃ X Th _ hx hs hs1 hα hα.le hφ hφ hTF hV hX hTh cl
  refine b.trans ?_
  have hxi1 : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have h2 : α + x ^ (-(1 / 2 : ℝ)) * α ≤ 2 * α := by
    nlinarith [mul_le_mul_of_nonneg_right hxi1 hα.le]
  have he : 0 ≤ Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₃)) := (Real.exp_pos _).le
  show c * (1 + ∑ q ∈ Finset.range 7, Cq q) * (T.E / T.η₃) * (α + x ^ (-(1 / 2 : ℝ)) * α) *
      Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c₃)) ≤ _
  have h3 : c * (1 + ∑ q ∈ Finset.range 7, Cq q) * (T.E / T.η₃) * (α + x ^ (-(1 / 2 : ℝ)) * α) ≤
      c * (1 + ∑ q ∈ Finset.range 7, Cq q) * (T.E / T.η₃) * (2 * α) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine (mul_le_mul_of_nonneg_right h3 he).trans (le_of_eq ?_)
  rw [hαd]
  field_simp
end Interpolation
end YangMills.Construction
end
