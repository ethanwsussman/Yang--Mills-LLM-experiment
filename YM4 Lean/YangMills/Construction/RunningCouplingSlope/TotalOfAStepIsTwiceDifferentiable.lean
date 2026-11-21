import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def StepGaugeTotalContDiff : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in Filter.atTop, ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
      ContDiffAt ℝ 2
        (fun σ : Fin k → ℝ => SlopeCoefficient.stepGaugeTotal a ρ L t n
          (TorusFields.perturb c X σ (TorusFields.trivialField n))) 0
end YangMills.Construction.RunningCouplingSlope
end
