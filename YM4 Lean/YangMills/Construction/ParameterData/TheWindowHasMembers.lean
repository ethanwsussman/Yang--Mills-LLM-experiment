import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open RenormalizationStepParameters
def passageWindowNonemptyAt {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    (∀ K₀ : ℕ, ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ K : ℕ, β ∈ D.passageWindow K g → K₀ ≤ K) ∧
    {K : ℕ | (D.passageWindow K g).Nonempty}.Infinite ∧
    ∀ K₀ : ℕ, ∃ K : ℕ, K₀ < K ∧ K ≤ K₀ + D.windowCount ∧ (D.passageWindow K g).Nonempty
def passageWindowNonemptyStatement : Prop :=
  ∀ (T : ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → passageWindowNonemptyAt D
end YangMills.Construction.TrajectoryData
end
