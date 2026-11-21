import YangMills.Construction.ResponseInTheExpansion.FunctionsOfTheCases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open StepCosts StepGas StepSettings RenormalizationStepParameters TorusFields
def caseMeanEqGasMeanStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    (∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ ∧
      0 < ∫ η, chartDensity (configSetting G σ) η) ∧
    ∀ F : CaseFunction R n,
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
        (b : BaseChoice R.params.side n),
        Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
      IsGaugeInvariantCase F → CaseIntegrable R G.cut G.coarse G.state F →
      Integrable (fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases)
        (G.gibbsLaw ∅) ∧
      caseMean R G.cut G.coarse G.state F = gasExpectationOfCase G F
end WeightedResponses
end YangMills.Construction
end
