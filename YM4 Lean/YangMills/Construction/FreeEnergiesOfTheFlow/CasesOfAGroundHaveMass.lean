import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FreeEnergiesOfTheFlow
open StepGas StepSettings WeightedResponses
def CoarseStateWeightNeZeroOnGround : Prop :=
  HoldsAtEveryStep fun _ R _ => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    coarseStateWeight R G.cut G.coarse G.state ≠ 0
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
