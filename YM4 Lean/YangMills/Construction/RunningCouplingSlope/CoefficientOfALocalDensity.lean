import YangMills.Construction.RunningCouplingSlope.LocalDensities
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def LocalDensityCoefficient.Claim : Prop :=
  ∀ (h : TorusLumps.LocalDensity) (H : SlopeCoefficient.GaugeTotal), IsLocalGaugeDensity h →
    (∀ᶠ n in Filter.atTop, SlopeCoefficient.IsGaugeTotalAt H n) →
    (∀ᶠ n in Filter.atTop, ∀ᶠ V in 𝓝 (TorusFields.trivialField n), centeredDensityTotal h n V = H n V) →
    ∃ b : ℝ, SlopeCoefficient.HasSlopeCoefficient Filter.atTop H b
end YangMills.Construction.RunningCouplingSlope
end
