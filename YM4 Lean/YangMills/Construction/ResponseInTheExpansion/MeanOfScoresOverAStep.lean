import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def ScoreProductStepMean : Prop :=
  ∀ (p : StepParameters), p.Admissible → 11 * 2 ^ 12 * p.baseDepth < p.side → ∀ (y : ℝ) (n : ℕ) [NeZero n]
    (W : TorusField (n * p.side)) (m : ℕ) (a : Fin m → ℝ) (v : Fin m → TorusBond n → ℝ),
    (∀ (c : TorusBond n) (i j : Fin m), i ≠ j → v i c = 0 ∨ v j c = 0) →
    ∑ b : BaseChoice p.side n, ∫ V : TorusField n, (∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore p y W V b c)) *
      stepTransitionDensity p y W b V ∂(fieldHaar n) = ∏ i, a i
end YangMills.Construction.WeightedResponses
end
