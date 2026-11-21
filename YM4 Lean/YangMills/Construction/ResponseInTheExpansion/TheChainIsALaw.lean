import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def initialMass (p : StepParameters) (β : ℝ) (s n : ℕ) [NeZero n] : ℝ :=
  ∫ W, wilsonWeight β (fineSide p.side s n) W ∂(fieldHaar (fineSide p.side s n))
def ChainIsProbabilityLaw : Prop :=
  ∀ (p : StepParameters), p.Admissible → 11 * 2 ^ 12 * p.baseDepth < p.side → ∀ (β : ℝ) (x : ℕ → ℝ) (s n : ℕ)
    [NeZero n],
    IsProbabilityMeasure (chainJointLaw p β x s n) ∧ 0 < initialMass p β s n ∧
    Measurable (chainFunctional p β x s n) ∧ (∀ V, 0 < chainFunctional p β x s n V) ∧
    (∃ C : ℝ, ∀ V, chainFunctional p β x s n V ≤ C) ∧
    (∀ V : TorusField n, Integrable (fun W : TorusField (n * p.side) => chainFunctional p β x s (n * p.side) W *
      averagedKernel p (x s) (readAtLevel (stepBlockFrame p.side n) 0 W)
        (readAtLevel (stepBlockFrame p.side n) 1 V)) (fieldHaar (n * p.side))) ∧
    ∫ V, chainFunctional p β x s n V ∂(fieldHaar n) = initialMass p β s n ∧
    (∀ G : TorusField n → ℝ, Measurable G → (∃ C : ℝ, ∀ V, |G V| ≤ C) →
      ∫ u, G (finalField p s n u) ∂(chainJointLaw p β x s n) =
        (∫ V, G V * chainFunctional p β x s n V ∂(fieldHaar n)) / initialMass p β s n) ∧
    ∀ G : TorusField (fineSide p.side s n) → ℝ, Measurable G → (∃ C : ℝ, ∀ W, |G W| ≤ C) →
      ∫ u, G (initialField p s n u) ∂(chainJointLaw p β x s n) =
        (∫ W, G W * wilsonWeight β (fineSide p.side s n) W ∂(fieldHaar (fineSide p.side s n))) /
          initialMass p β s n
end YangMills.Construction.WeightedResponses
end
