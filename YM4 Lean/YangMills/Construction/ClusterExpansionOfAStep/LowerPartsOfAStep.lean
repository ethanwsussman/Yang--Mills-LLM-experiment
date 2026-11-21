import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AvoidingParts
open BlockAverages LumpContours TorusFields StepSettings
def AvoidingPartNonnegAntitone : Prop :=
  ∀ R : StepSetup, R.HasExpansions → ∀ n [NeZero n], R.params.n₀ ≤ n →
    ∀ W : TorusField (n * R.params.side),
    (∀ A : Finset (TorusSite n), 0 ≤ R.avoidingPart A W) ∧
    ∀ A B : Finset (TorusSite n), B ⊆ A → R.avoidingPart A W ≤ R.avoidingPart B W
end YangMills.Construction.AvoidingParts
end
