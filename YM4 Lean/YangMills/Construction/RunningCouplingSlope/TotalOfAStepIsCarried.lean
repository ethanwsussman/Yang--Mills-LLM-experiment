import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open TorusFields SlopeCoefficient Conventions
def StepGaugeTotalIsometryInvariant : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in Filter.atTop, ∀ g : TorusIsometry, ∀ᶠ V in 𝓝 (trivialField n), ∀ V' : TorusField n,
      g.Transports V V' → stepGaugeTotal a ρ L t n V' = stepGaugeTotal a ρ L t n V
end YangMills.Construction.RunningCouplingSlope
end
