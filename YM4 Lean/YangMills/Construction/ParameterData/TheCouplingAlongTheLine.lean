import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def CouplingAlongLineAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ k ≤ K,
      |D.coupling β k - D.coupling β K - D.c₀ * ((K : ℝ) - k)| ≤ D.lineGap (K - k)
def couplingAlongLineStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → CouplingAlongLineAt D
end YangMills.Construction.TrajectoryData
end
