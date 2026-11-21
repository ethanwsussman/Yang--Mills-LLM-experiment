import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def CouplingNearFlowAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g →
      (∀ k ≤ K, |D.coupling β k - D.numberFlow β k| ≤ 2 * D.Cr * D.coupling β k ^ (-(1 / 4) : ℝ)) ∧
      |D.coupling β K - D.numberFlow β K| ≤ 2 * D.Cr * g ^ (1 / 2 : ℝ)
def couplingNearFlowStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → CouplingNearFlowAt D
end YangMills.Construction.TrajectoryData
end
