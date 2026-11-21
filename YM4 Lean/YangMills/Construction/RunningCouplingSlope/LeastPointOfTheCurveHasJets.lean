import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.TheCurveInTheVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages RenormalizationStepParameters StepSettings TorusFields
namespace RunningCouplingSlope
def MinimizerCoordinatesJetBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ k : ℕ, ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), T.n₀ ≤ n →
        AreUnitVectors X →
        minimizerCoordinatesAlong R n c X 0 = 0 ∧
        ContDiffAt ℝ 5 (minimizerCoordinatesAlong R n c X) 0 ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
          ‖iteratedFDeriv ℝ j (minimizerCoordinatesAlong R n c X) 0‖ ≤ C * (n : ℝ) ^ q
end RunningCouplingSlope
end YangMills.Construction
end
