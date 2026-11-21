import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusFields StepSettings RenormalizationStepParameters ColdStepAtMirrorFrames WeightedResponses
def MarkLawMeasurable : Prop :=
  ∀ (T : ParameterAssignment), T.Admissible → ∀ (y : ℝ) (R : StepSetup), R.params = T.stepParameters y →
    R.params.Admissible → R.anchorRadius = T.ρA →
    IsCutoff R.ballRadius R.barrierFn → 16 ≤ R.frameReach → R.frameReach + 2 ≤ R.nextRange →
    ∀ (n : ℕ) [NeZero n], R.params.side ∣ n → 64 ≤ n →
      ∀ bad : Finset (TorusBond (n * R.params.side)),
        Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad
end ResponseInTheExpansion
end YangMills.Construction
end
