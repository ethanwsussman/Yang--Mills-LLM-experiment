import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters StepSettings WeightedResponses
def gasTermBoundsStatement : Prop :=
  ∃ rtMax : ChainParameters → ℝ, (∀ c, 0 < rtMax c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.HoldsFrom ColdRegimeEstimatesAt → T.rt ≤ rtMax T.toChainParameters → ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ResponseParameters, ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = K → OnStepParameters T y A → R.IsSymmetricWeight →
      TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
        (C * R.coupling ^ (-(3 / 2) : ℝ)) (gasTerm A)
end YangMills.Construction.ResponseInTheExpansion
end
