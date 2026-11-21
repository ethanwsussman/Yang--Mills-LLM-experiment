import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
def ExpDecaySumAndBallCard : Prop :=
  (∀ c : ℝ, 0 < c → ∃ M : ℝ, ∀ (N : ℕ) [NeZero N] (z : TorusSite N),
    ∑ a : TorusSite N, Real.exp (-(c * (supDist a z : ℝ))) * (1 + (supDist a z : ℝ)) ≤ M) ∧
  ∀ (N : ℕ) [NeZero N] (z : TorusSite N) (R : ℕ),
    (Finset.univ.filter fun a : TorusSite N => supDist a z ≤ R).card ≤ (2 * R + 1) ^ 4
end YangMills.Construction.TorusFields
end
