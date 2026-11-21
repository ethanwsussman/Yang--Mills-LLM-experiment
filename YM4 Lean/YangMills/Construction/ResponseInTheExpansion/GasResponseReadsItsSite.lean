import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepGas BlockAverages
def gasResponseShift_local : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n,
    IsCold (9 / 8 * R.params.threshold) V →
    ∀ (y : TorusSite (n * R.params.side)) (f f' : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      (∀ p, IsPlaquetteAt R.params.side R.depth y p → f p = f' p) →
      gasResponseShift A (coldCaseGround R V) y f = gasResponseShift A (coldCaseGround R V) y f'
end YangMills.Construction.WeightedResponses
end
