import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TopAux.SchwingerSequenceExists
def Statement : Prop :=
  ∃ (σ : SeparatedTuples.TupleFunctional) (T : ConfigSpace.FlatSequence),
    SystemsWithFiveBounds.HasSchwingerSequence σ T
end YangMills.Construction.TopAux.SchwingerSequenceExists
end
