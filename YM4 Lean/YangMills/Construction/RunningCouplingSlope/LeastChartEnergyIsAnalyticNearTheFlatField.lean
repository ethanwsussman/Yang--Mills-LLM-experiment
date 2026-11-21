import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.SlopeCoefficient
def ChartedEnergyAnalyticNearTrivial : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (t n : ℕ) (ρ : ℝ), 2 * L ≤ n → 0 < ρ → ρ ≤ 1 →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField n),
      AnalyticAt ℝ (ReferenceDensity.chartedEnergyAtMinimizer (F := TorusFields.torusFrame L t n) a ρ
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)) 0
end YangMills.Construction.SlopeCoefficient
end
