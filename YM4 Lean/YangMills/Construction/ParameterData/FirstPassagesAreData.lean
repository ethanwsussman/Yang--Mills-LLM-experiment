import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def WindowMembersAreDataAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ (K : ℕ) (β : ℝ), 2 ≤ K → β ∈ D.passageWindow K g → D.IsDatum g K β
def windowMembersAreDataStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → WindowMembersAreDataAt D
end YangMills.Construction.TrajectoryData
end
