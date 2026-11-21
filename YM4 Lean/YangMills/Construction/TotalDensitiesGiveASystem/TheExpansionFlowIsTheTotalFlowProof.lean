import YangMills.Construction.SummableBoundsOfTheFlow.SummabilityBounds
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.WindowOfTheParameters.DataOfTheTotalFlowAreThoseOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
theorem expansionFlowEqTotalFlow_of_bound (hbudget : CouplingFlow.FlowEstimateExists)
    (hwindow : TotalDensityFlow.PassageWindowEqExpansionWindow) :
    expansionFlowEqTotalFlow := by
  obtain ⟨Q, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, h1, h2, hT⟩ := hbudget
  refine ⟨⟨Q, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs, fun _ => 0⟩, ⟨hQ, h1, h2⟩, fun T hD hM => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hD hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.derivBound_ge hM.holds
  refine ⟨y₀, fun y hy Bs hBs => ?_⟩
  obtain ⟨c, M, R, X, Cr, v₀, mw, hb⟩ := f y hy
  refine ⟨X, fun g hg hX K => ?_⟩
  have hBs : 0 ≤ Bs := by
    have := hD.B_ge
    linarith
  have hc : 0 ≤ c := by
    have h := hb.slope 0 0 le_rfl
    simp at h
    exact h
  have hflow : FloorBounds.FlowAboveFloor T y c X :=
    ⟨hb.admissible, hb.slope_gt, hc, hb.floor_le, hb.drop_two_sided, hb.expansion⟩
  exact hwindow T y c X hD hflow Bs g hBs hg hX K
end YangMills.Construction.TotalDensities
end
