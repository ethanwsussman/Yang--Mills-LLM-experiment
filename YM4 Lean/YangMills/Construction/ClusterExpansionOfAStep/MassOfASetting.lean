import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def SettingMassEqIntegral : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ s : ChartSetting S n, s.IsAdmissible →
        Integrable (fun η => s.cutoffProduct η * Real.exp (-s.potential η)) ∧
        0 < ∫ η, s.cutoffProduct η * Real.exp (-s.potential η) ∧
        settingMass s = ENNReal.ofReal (∫ η, s.cutoffProduct η * Real.exp (-s.potential η))
end YangMills.Construction.StepGas
end
