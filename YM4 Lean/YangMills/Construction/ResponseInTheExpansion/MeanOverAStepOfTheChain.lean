import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def ChainStepMean : Prop :=
  ∀ (p : StepParameters) (β : ℝ) (x : ℕ → ℝ),
    (∀ (s n : ℕ) [NeZero n], IsFiniteMeasure (chainJointLaw p β x s n)) ∧
    (∀ (n : ℕ) [NeZero n] (g : TorusField n → ℝ), ∫ u, g u ∂(chainJointLaw p β x 0 n) =
      ∫ W, wilsonWeight β n W / (∫ W', wilsonWeight β n W' ∂(fieldHaar n)) * g W ∂(fieldHaar n)) ∧
    ∀ (s n : ℕ) [NeZero n] (F : ChainSample p (s + 1) n → ℝ) (G : ChainSample p s (n * p.side) → ℝ),
      Measurable F → (∃ C : ℝ, ∀ u, |F u| ≤ C) →
      (∀ u : ChainSample p s (n * p.side), ∑ b : BaseChoice p.side n, ∫ V : TorusField n,
        F (u, b, V) * stepTransitionDensity p (x s) (finalField p s (n * p.side) u) b V ∂(fieldHaar n) = G u) →
      ∫ u, F u ∂(chainJointLaw p β x (s + 1) n) = ∫ u, G u ∂(chainJointLaw p β x s (n * p.side))
end YangMills.Construction.WeightedResponses
end
