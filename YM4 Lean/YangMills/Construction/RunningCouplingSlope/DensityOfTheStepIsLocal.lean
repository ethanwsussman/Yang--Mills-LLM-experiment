import YangMills.Construction.RunningCouplingSlope.LocalDensities
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open TorusFields RenormalizationStepParameters ReferenceDensity SlopeCoefficient
namespace RunningCouplingSlope
def StepDensityIsLocal.Claim : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ t : ℕ,
    IsLocalGaugeDensity (stepDensityFamily T.coupling T.ρA T.lam T.side t) ∧
      ∀ᶠ n in Filter.atTop, ∀ᶠ V in 𝓝 (trivialField n),
        centeredDensityTotal (stepDensityFamily T.coupling T.ρA T.lam T.side t) n V =
          stepGaugeTotal T.coupling T.ρA T.side t n V
end RunningCouplingSlope
end YangMills.Construction
end
