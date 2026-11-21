import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
def ContinuousAtOfContDiffThreeAt : Prop :=
  ∀ (m : ℕ) [NeZero m] (G : TorusField m → ℝ) (W : TorusField m), ContDiffThreeAt G W → ContinuousAt G W
end YangMills.Construction.TorusFields
end
