import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace StateLaws
def emptyLabelling {n : ℕ} (Ω : Type) : (∅ : Finset (TorusFields.TorusSite n)) → Ω :=
  fun z => absurd z.2 (Finset.notMem_empty _)
end StateLaws
end YangMills.Construction
