import YangMills.Construction.LawByMomentsOfTheFlow.NearlyLocalFunctionsOfTheCases
import YangMills.Construction.LawInAState.LocalFunctionsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def nearlyLocalSettingFactorizationStatement : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (s : StepSettings.ChartSetting R n), R.params.n₀ ≤ n → s.IsAdmissible →
      ∀ (p : ℕ) (Q : Fin p → ResponseInTheExpansion.StateFunction R (n * R.params.side))
        (z : Fin p → TorusFields.TorusSite (n * R.params.side)) (K ρ : ℝ) (D : ℕ),
        1 ≤ p → p ≤ 16 → 0 ≤ ρ → (∀ i, IsNearlyLocalStateFunction R (Q i) (z i) K ρ) →
        2 ^ 10 * ((R.range : ℝ) + ρ) ≤ D →
        (∀ i j, i ≠ j → D ≤ TorusFields.supDist (TorusLumps.parentBlock R.params.side (z i))
          (TorusLumps.parentBlock R.params.side (z j))) →
        |StepSettings.weightedMean (WeightedResponses.chartDensity s)
            (fun η => ∏ i, Q i (s.field η) s.support s.labelling) -
          ∏ i, StateLaws.settingMean s (Q i)| ≤
          C * K ^ p * Real.exp (-(R.params.rt * D / 2 ^ 4))
end YangMills.Construction.MomentLaw
end
