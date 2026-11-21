import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainLogarithmIsGaugeTotal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (k : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in Filter.atTop, SlopeCoefficient.IsGaugeTotalAt (SlopeCoefficient.chainLogarithm a ρ L k) n
end YangMills.Construction.RunningCouplingSlope
end
