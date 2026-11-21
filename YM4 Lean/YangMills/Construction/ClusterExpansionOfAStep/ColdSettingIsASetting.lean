import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
def ColdChartSettingIsAdmissible : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold (9 / 8 * T.threshold) V →
      (coldChartSetting R V).IsAdmissible
end YangMills.Construction.StepSettings
end
