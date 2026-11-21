import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.SlopeCoefficient
def StepGaugeTotalInvariant : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in Filter.atTop, ∀ᶠ p : (TorusFields.TorusSite n → BlockAverages.UnitQuaternion) × TorusFields.TorusField n
      in 𝓝 (1, TorusFields.trivialField n),
      SlopeCoefficient.stepGaugeTotal a ρ L t n (TorusFields.gaugeTransform p.1 p.2) =
        SlopeCoefficient.stepGaugeTotal a ρ L t n p.2
end YangMills.Construction.SlopeCoefficient
end
