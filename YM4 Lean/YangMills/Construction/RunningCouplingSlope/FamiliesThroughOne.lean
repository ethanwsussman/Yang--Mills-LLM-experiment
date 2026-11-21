import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
variable {L n k : ℕ}
structure IsAnalyticFamilyThroughUnit {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → ChainPoint L n k) (p₀ : E) : Prop where
  eq_unit : X p₀ = unitPoint L n k
  analyticAt_fine : ∀ b, AnalyticAt ℝ (fun p => (X p).fine b) p₀
  analyticAt_noise : ∀ i c, AnalyticAt ℝ (fun p => (X p).noise i c) p₀
  eventually_compact : ∀ᶠ p in 𝓝 p₀, (X p).fine ∈ Tower.fieldSpace L n k 0 ∧
    ∀ i c, (X p).noise i c ∈ PeriodicLattice.compactGaugeGroup
end RunningCouplingSlope
end YangMills.Construction
end
