import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.TheCurveInTheVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusFields TorusLumps
namespace RunningCouplingSlope
def ChartedEnergyJetBounds : Prop :=
  ∀ P : ParameterAssignment, P.Admissible → ∀ k : ℕ, ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (y : ℝ) (S : StepSetup), P.floorMin ≤ y → S.OnParameters P y →
      ∀ (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        P.n₀ ≤ n → AreUnitVectors X →
        ∀ ζ : StepVariable (finiteCells (torusFrame S.params.side S.depth n)),
          (∀ b, ‖ζ b‖ ≤ P.ballRadius) →
          ContDiffAt ℝ 5 (chartedEnergyAlong S n c X) (ζ, 0) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
            ‖iteratedFDeriv ℝ j (chartedEnergyAlong S n c X) (ζ, 0)‖ ≤ C * (n : ℝ) ^ q
end RunningCouplingSlope
end YangMills.Construction
end
