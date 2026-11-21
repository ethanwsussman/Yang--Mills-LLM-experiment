import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions
namespace SlopeCoefficient
def StepGaugeTotalIsGaugeTotal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in Filter.atTop, IsGaugeTotalAt (stepGaugeTotal a ρ L t) n
end SlopeCoefficient
end YangMills.Construction
end
