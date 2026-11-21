import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusSums
open TorusFields
def ExpDecaySumBounded : Prop :=
  ∀ c : ℝ, 0 < c → ∃ S : ℝ, 0 ≤ S ∧ ∀ (n : ℕ) [NeZero n] (y : TorusSite n),
    ∑ s : TorusSite n, Real.exp (-(c * (supDist s y : ℝ))) * (1 + (supDist s y : ℝ)) ^ 5 ≤ S
end YangMills.Construction.TorusSums
end
