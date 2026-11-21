import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensityFlow
open TorusLumps WeightedResponses RenormalizationStepParameters
def ExpansionGivesFlow : Prop :=
  ∀ (T : ParameterAssignment) (z : ℝ), T.Admissible → (T.stepParameters z).Admissible →
    Conventions.IsAdmissibleBlockingFactor (T.stepParameters z).side →
    ∀ (β : ℝ) (t : ℕ) (y : ℕ → ℝ), y 0 = β → (∀ k < t, (T.stepParameters z).y₁ ≤ y k) →
      (∀ k ≤ t, HasExpansion (T.stepParameters z) k (y k) (chainFunctional (T.stepParameters z) β y k)) →
        IsFlowUpTo (T.stepParameters z) β t y
end YangMills.Construction.TotalDensityFlow
end
