import YangMills.Construction.WindowOfTheParameters.CoefficientAsAMixedMoment
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TopAux
def flowReadsMixedMomentStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ), 2 ≤ ℓ.side → TotalDensityFlow.IsDefinedUpTo ℓ β t →
    ∀ j < t, ∀ b : ℝ,
      SlopeCoefficient.HasMixedSecondMoment (TotalDensityFlow.sideFilter ℓ.side)
          (TotalDensityFlow.logRatio
            (WeightedResponses.chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) (j + 1))) b ↔
        b = -TotalDensityFlow.coupling ℓ β (j + 1)
end TopAux
end YangMills.Construction
end
