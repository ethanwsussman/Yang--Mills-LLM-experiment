import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawInTheLimitsProof
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawOnTheWindow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open RenormalizationStepParameters TrajectoryData FourPointCondition TotalDensities
private theorem trajectoryParameters_holdsAtAdmissibleSchedules (hFlowData : TrajectoryData.trajectoryDataStatement) :
    HoldsAtAdmissibleParameters fun T y => ∃ D : TrajectoryParameters T y, HasTrajectoryDataForAllShifts D := by apply _root_.YangMills.SharedProofs.p67844 <;> assumption
private theorem rateBound_pos {T : ParameterAssignment} {y : ℝ} (hAdm : T.Admissible) (D : TrajectoryParameters T y) :
    0 < D.rateBound := by
  have hside : (1 : ℝ) < T.side := by
    have h : 1 < T.side := lt_of_lt_of_le (by norm_num) hAdm.L_ge
    exact_mod_cast h
  have hlog := Real.log_pos hside
  show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
  positivity
theorem fourPointLawOnWindow_of_components (hResponseAdmissible : ResponseParametersToAdmissibleParameters)
    (hFlowData : TrajectoryData.trajectoryDataStatement) (hCentered : fourPointBoundAtFlowDataStatement)
    (hLaws : lawsAtFlowDataStatement) : fourPointLawOnWindow := by
  refine HoldsAtAdmissibleParameters.mono
    (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (hResponseAdmissible _ hCentered) (hResponseAdmissible _ hLaws))
      (trajectoryParameters_holdsAtAdmissibleSchedules hFlowData)) ?_
  rintro T y hAdm ⟨⟨hCl, _, -, hLw⟩, D, hData⟩ Bs hBs
  obtain ⟨al, -, hAt⟩ := hLw D hData
  refine ⟨D.floorStar, fun g hg hy => ⟨hCl D hData Bs hBs g hg hy, fun room hroom => ?_⟩⟩
  obtain ⟨d₀, ηBar, εBar, hPullback, hSharp, -⟩ :=
    hAt Bs D.rateBound hBs (rateBound_pos hAdm D) le_rfl 1 one_pos le_rfl g hg hy room hroom
  refine ⟨d₀, ηBar, hPullback.d₀_mem, hSharp.ηBar_tendsto, ?_⟩
  intro _ K β hPoint d hd hDeep
  exact hSharp.log_le K β hPoint d hd hDeep
end YangMills.Construction.TotalDensitiesGiveASystem
end
