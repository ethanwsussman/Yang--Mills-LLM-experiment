import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SummableBounds
open ColdStepAtMirrorFrames
def couplingAtLeastOneStatement : Prop :=
  ∀ R : StepParameters → Prop, EventuallyInParameters R →
    EventuallyInParameters fun T => R T ∧ 1 ≤ T.coupling
end SummableBounds
end YangMills.Construction
end
