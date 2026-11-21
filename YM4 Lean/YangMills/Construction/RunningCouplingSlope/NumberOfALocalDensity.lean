import YangMills.Construction.RunningCouplingSlope.LocalDensities
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def CoefficientFromDensity.Claim : Prop :=
  ∀ (h : TorusLumps.LocalDensity) (H : SlopeCoefficient.GaugeTotal) (b : ℝ), IsLocalGaugeDensity h →
    SlopeCoefficient.HasSlopeCoefficient Filter.atTop H b →
    (∀ᶠ n in Filter.atTop, ∀ᶠ V in 𝓝 (TorusFields.trivialField n), centeredDensityTotal h n V = H n V) →
    HasSum (TorusLumps.limitFormTerm h TorusLumps.unitPlaneCurvature TorusLumps.unitPlaneCurvature) b
end YangMills.Construction.RunningCouplingSlope
end
