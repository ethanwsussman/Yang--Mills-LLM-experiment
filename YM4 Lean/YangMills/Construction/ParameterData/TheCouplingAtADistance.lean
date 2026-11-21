import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def CouplingAtDistanceAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ p : ℝ, 0 ≤ p → ∃ e : ℝ → ℝ, Filter.Tendsto e (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (K : ℕ) (β : ℝ), 2 ≤ K → β ∈ D.passageWindow K g → ∀ k ≤ K, ∀ d : ℝ, d < 1 →
        1 ≤ d / (T.side : ℝ) ^ ((k : ℤ) - K) → d / (T.side : ℝ) ^ ((k : ℤ) - K) ≤ D.coupling β k ^ p →
        |D.coupling β k / (logSlope * Real.log (1 / d)) - 1| ≤ e d
def couplingAtDistanceStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → CouplingAtDistanceAt D
end YangMills.Construction.TrajectoryData
end
