import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open Conventions TorusFields
namespace SlopeCoefficient
def StepGaugeTotalIndependentOfCutoff : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ ρ' : ℝ), 0 < ρ → ρ ≤ 1 → 0 < ρ' → ρ' ≤ 1 →
    ∀ᶠ n in Filter.atTop, ∀ᶠ V in 𝓝 (trivialField n), stepGaugeTotal a ρ L t n V = stepGaugeTotal a ρ' L t n V
end SlopeCoefficient
end YangMills.Construction
end
