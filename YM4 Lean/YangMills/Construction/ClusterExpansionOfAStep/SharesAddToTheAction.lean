import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepCosts
open YangMills.Construction.TorusFields
def SharesSumToAction : Prop :=
  ∀ (a : ℝ) (L t n : ℕ) [NeZero n] (S : Finset (TorusSite n)) (V : TorusField n), 0 ≤ a → 0 < L → 2 ≤ n →
    ∑ y : TorusSite n, levelShare a L (t + 1) S y V = actionAtLevel a L (t + 1) S V
end YangMills.Construction.StepCosts
end
