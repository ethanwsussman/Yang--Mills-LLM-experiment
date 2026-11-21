import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames FamilyNorms RenormalizationStepParameters WeightedResponses StepSettings TorusFields BlockAverages
structure ResponseTermDecomposition {R : StepSetup} (A : ResponseSetup R) (C : ℝ) : Prop where
  frame_bounds : TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
    (C * R.coupling ^ (-(3 / 2) : ℝ)) (frameTerm A)
  linear_bounds : TermBounds R.params (C / R.coupling) (C / R.coupling) (C / R.coupling) (linearTerm A)
  increment_bounds : TermBounds R.params (C * R.coupling ^ (-(1 / 2) : ℝ)) (C * R.coupling ^ (-(1 / 2) : ℝ))
    (C * R.coupling ^ (-(1 / 2) : ℝ)) (incrementTerm A)
  remainder_bounds : TermBounds R.params (2⁻¹ ^ 5 * (A.responseParams.Kb / R.coupling))
    (2⁻¹ ^ 5 * (A.responseParams.Kb / R.coupling / A.responseParams.η₃))
    (2⁻¹ ^ 4 * (A.responseParams.Kb / R.coupling)) (remainderTerm A)
  remainder_planeValue : ∃ v, HasUnitPlaneValue (remainderTerm A) v ∧
    |v| ≤ C * (A.responseParams.Kb / R.coupling) * R.coupling ^ (-(1 / 2) : ℝ)
  scoreTail_bounds : TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
    (C * R.coupling ^ (-(3 / 2) : ℝ)) (scoreTailTerm A)
  gas_bounds : TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
    (C * R.coupling ^ (-(3 / 2) : ℝ)) (gasTerm A)
  linear_sum : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
    ∑ Y, linearTerm A n Y V = A.coeff * (coldHalfLawOf R).expectation (coldTopField R V)
      (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) - (coldHalfLawOf R).totalCost 0 (coldTopField R V))
  isTotalRemainder : IsTotalRemainder R.params A.coldStep A.coeff (totalRemainderOfTerms A)
def responseTermDecompositionStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds → T.HoldsFrom ColdRegimeEstimatesAt →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ResponseParameters, 0 < K.Kb → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSetup) (A : ResponseSetup R),
      A.responseParams = K → OnStepParameters T y A → R.IsSymmetricWeight → ResponseTermDecomposition A C
end YangMills.Construction.ResponseInTheExpansion
end
