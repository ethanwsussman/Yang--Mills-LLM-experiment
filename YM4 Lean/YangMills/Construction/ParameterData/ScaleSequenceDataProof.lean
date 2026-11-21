import YangMills.Construction.ParameterData.ScaleSequenceData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
theorem trajectoryData_of_conditions
    (hFlowBound : YangMills.Construction.CouplingFlow.FlowEstimateExists)
    (hPassage : firstPassageExistsStatement)
    (hData : windowMembersAreDataStatement)
    (hMembers : passageWindowNonemptyStatement)
    (hLine : couplingAlongLineStatement)
    (hRatio : betaLogCutoffRatioStatement)
    (hDistance : couplingAtDistanceStatement)
    (hFlow : couplingNearFlowStatement)
    (hSlope : couplingDecreaseStatement) :
    trajectoryDataStatement := by
  obtain ⟨Q, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, hRt, hσ, hOnParameters⟩ := hFlowBound
  refine ⟨Q, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, hRt, hσ, ?_⟩
  intro T hT hL hrt hs hN hCs hC hOn
  obtain ⟨y₀, hFloor⟩ := hOnParameters T hT hL hrt hs hN hCs hC hOn
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨c, M, R, X, Cr, v₀, mw, hb⟩ := hFloor y hy
  let D : TrajectoryParameters T y :=
    { cH := c, Md := M, R := R, X₀ := X, Cr := Cr, mw := mw, v₀ := v₀, shift := 2 * T.B,
      lam := 3 / 4 * YangMills.Construction.CouplingFlow.slopeConst T.side }
  refine ⟨D, fun shift lam hshift hlam hle => ?_⟩
  have hAdm : (D.withShift shift lam).Admissible :=
    { errorMargin := hb, shift_ge := hshift, lam_pos := hlam, lam_le := hle }
  exact ⟨hAdm,
    { passage := hPassage T y _ hAdm
      data := hData T y _ hAdm
      members := hMembers T y _ hAdm
      line := hLine T y _ hAdm
      ratio := hRatio T y _ hAdm
      distance := hDistance T y _ hAdm
      flow := hFlow T y _ hAdm
      slope := hSlope T y _ hAdm }⟩
end YangMills.Construction.TrajectoryData
end
