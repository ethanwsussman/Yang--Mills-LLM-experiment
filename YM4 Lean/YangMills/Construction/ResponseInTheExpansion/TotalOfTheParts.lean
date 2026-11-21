import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames Interpolation RenormalizationStepParameters StepSettings WeightedResponses TorusFields
def sumOfTermsStatement : Prop :=
  ∃ rtMax : ChainParameters → ℝ, (∀ c, 0 < rtMax c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.HoldsFrom ColdRegimeEstimatesAt → T.rt ≤ rtMax T.toChainParameters → ∀ K : ResponseParameters,
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ (R : StepSetup) (A : ResponseSetup R),
      A.responseParams = K → OnStepParameters T y A →
      (∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
        ∑ Y, linearTerm A n Y V = A.coeff * (coldHalfLawOf R).expectation (coldTopField R V)
          (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) - (coldHalfLawOf R).totalCost 0 (coldTopField R V))) ∧
      IsTotalRemainder R.params A.coldStep A.coeff (totalRemainderOfTerms A)
end YangMills.Construction.ResponseInTheExpansion
end
