import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
open YangMills.Construction.TorusFields
def ExpDecayTorusSumBounded : Prop :=
  ∀ c : ℝ, 0 < c → ∃ S : ℝ, 0 < S ∧ ∀ (n : ℕ) [NeZero n] (y : TorusSite n),
    ∑ x : TorusSite n, Real.exp (-(c * supDist y x)) ≤ S
end YangMills.Construction.SlopeCoefficient
end
