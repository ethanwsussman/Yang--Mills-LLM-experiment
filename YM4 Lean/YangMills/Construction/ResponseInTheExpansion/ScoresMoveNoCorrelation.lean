import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def ScoresPreserveCorrelations : Prop :=
  ∀ (p : StepParameters), p.Admissible → 11 * 2 ^ 12 * p.baseDepth < p.side → ∀ (β : ℝ) (x : ℕ → ℝ) (s n : ℕ)
    [NeZero n] (m : ℕ) (X : Fin m → TorusField (fineSide p.side s n) → ℝ) (w : ScoreWeights p m s n)
    (k : Fin m → ℝ),
    (∀ i, Measurable (X i)) → (∀ i, ∃ C : ℝ, ∀ W, |X i W| ≤ C) → ScoreWeights.Disjoint s n w →
    ∫ u, ∏ i, (X i (initialField p s n u) + weightedScoreSum p x s n w i u - k i) ∂(chainJointLaw p β x s n) =
      ∫ u, ∏ i, (X i (initialField p s n u) - k i) ∂(chainJointLaw p β x s n)
end YangMills.Construction.WeightedResponses
end
