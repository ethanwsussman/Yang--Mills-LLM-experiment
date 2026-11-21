import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def BetaLogCutoffRatioAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    Filter.Tendsto (D.ratioError g) Filter.atTop (nhds 0) ∧
    ∀ (K : ℕ) (β : ℝ), 1 ≤ K → β ∈ D.passageWindow K g →
      |β / Real.log (1 / (T.side : ℝ) ^ (-(K : ℤ))) - logSlope| ≤ D.ratioError g K
def betaLogCutoffRatioStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → BetaLogCutoffRatioAt D
end YangMills.Construction.TrajectoryData
end
