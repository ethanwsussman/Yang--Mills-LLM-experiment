import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def GaugeTotalAtMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ H : SlopeCoefficient.GaugeTotal, (∀ᶠ n in Filter.atTop, SlopeCoefficient.IsGaugeTotalAt H n) →
      ∀ᶠ n in Filter.atTop, SlopeCoefficient.IsGaugeTotalAt (atMinimizer a ρ L t H) n
end YangMills.Construction.RunningCouplingSlope
end
