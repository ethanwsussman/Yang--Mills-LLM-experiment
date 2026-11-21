import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopSlope
open RenormalizationStepParameters CouplingFlow ReferenceDensity
def OneLoopCoefficientsHaveSlope : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∀ L : ℕ, Odd L → 13 ≤ L → ∃ c : ℝ, ∀ T : ParameterAssignment, T.Admissible → T.coupling = a →
    T.side = L → HasAverageSlope (oneLoopCoefficient T.coupling T.ρA T.lam T.side) (slopeConst L) c
end YangMills.Construction.OneLoopSlope
end
