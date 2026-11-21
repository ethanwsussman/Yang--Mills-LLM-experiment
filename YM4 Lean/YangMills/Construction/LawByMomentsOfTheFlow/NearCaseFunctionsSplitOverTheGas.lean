import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.LawByMomentsOfTheFlow.NearlyLocalFunctionsOfTheCases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def nearCaseFunctionsSplitStatement : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∀ Kr : WeightedResponses.ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSettings.StepSetup) (A : WeightedResponses.ResponseSetup R), A.responseParams = Kr →
      WeightedResponses.OnStepParameters T y A → ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n),
      G.IsAdmissibleGround →
      ∀ (p : ℕ) (F : Fin p → WeightedResponses.CaseFunction R n)
        (z : Fin p → TorusFields.TorusSite (n * R.params.side)) (K : ℝ) (ρ D : ℕ),
        p ≤ 16 → (∀ i, IsNearlyLocalCaseFunction R (z i) ρ K (F i)) → 2 ^ 10 * ((R.range : ℝ) + ρ) ≤ D →
        (∀ i j, i ≠ j → D ≤ TorusFields.supDist (TorusLumps.parentBlock R.params.side (z i))
          (TorusLumps.parentBlock R.params.side (z j))) →
        |G.expectation ∅ (fun σ => ∏ i, FreeEnergies.settingMean (WeightedResponses.configSetting G σ)
            (G.badBondsOf σ) (F i)) -
          ∏ i, G.expectation ∅ (fun σ => FreeEnergies.settingMean (WeightedResponses.configSetting G σ)
            (G.badBondsOf σ) (F i))| ≤
          C * K ^ p * Real.exp (-(R.params.rt * D / 2 ^ 7))
end YangMills.Construction.MomentLaw
end
