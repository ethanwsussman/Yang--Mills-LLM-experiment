import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def StepTransitionDensityBounds : Prop :=
  ∀ (p : StepParameters) (x : ℝ) (n : ℕ) [NeZero n],
    (∀ b : BaseChoice p.side n,
      Measurable fun q : TorusField (n * p.side) × TorusField n => stepTransitionDensity p x q.1 b q.2) ∧
    ∃ C : ℝ, ∀ (W : TorusField (n * p.side)) (b : BaseChoice p.side n) (V : TorusField n),
      0 ≤ stepTransitionDensity p x W b V ∧ stepTransitionDensity p x W b V ≤ C
end YangMills.Construction.WeightedResponses
end
