import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields StepSettings RenormalizationStepParameters
namespace StepSettings
def ColdChartSettingIsCold : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      ∀ η : FreeCoords (coldChartSetting R V).free, (coldChartSetting R V).InBalls η →
        IsCold (T.threshold / 4) ((coldChartSetting R V).field η)
end StepSettings
end YangMills.Construction
end
