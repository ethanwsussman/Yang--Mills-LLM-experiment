import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusLumps WeightedResponses
def StageStatesMeasurableStatement : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (s n : ℕ) [NeZero n], Measurable (stageState T s n)
end ResponseInTheExpansion
end YangMills.Construction
end
