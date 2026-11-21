import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def TorusSumBounds : Prop :=
  ∀ (n : ℕ) [NeZero n] (y' : TorusSite n),
    (∀ κ : ℝ, 0 < κ →
      ∑ y : TorusSite n, Real.exp (-(κ * (supDist y y' : ℝ))) ≤ (2 / (1 - Real.exp (-(κ / 4)))) ^ 4) ∧
    ∀ m : ℕ, (((Finset.univ.filter fun y : TorusSite n => supDist y y' ≤ m).card : ℕ) : ℝ) ≤
      (2 * (m : ℝ) + 1) ^ 4
end YangMills.Construction.TorusLumps
end
