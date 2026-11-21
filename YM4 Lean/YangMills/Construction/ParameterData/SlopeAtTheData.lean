import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def CouplingDecreaseAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ i j : ℕ, i ≤ j → j ≤ K →
      D.rateBound * ((j : ℝ) - i) - D.c₅ ≤ D.coupling β i - D.coupling β j
def couplingDecreaseStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → CouplingDecreaseAt D
end YangMills.Construction.TrajectoryData
end
