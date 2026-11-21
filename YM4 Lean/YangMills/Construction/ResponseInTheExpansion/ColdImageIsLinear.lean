import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields
def coldStepLinearLocalStatement : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusSite n) (V : TorusField n),
    IsCold R.params.threshold V →
    (∀ (c : ℝ) (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
      A.coldStep n Y V (c • h + h') = c * A.coldStep n Y V h + A.coldStep n Y V h') ∧
    ∀ h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      (∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y p → h p = h' p) →
      A.coldStep n Y V h = A.coldStep n Y V h'
end YangMills.Construction.ResponseInTheExpansion
end
