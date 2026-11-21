import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts
def ClusterExpansionOfAStep.ContourMeanAtColdField : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      ∀ η : FreeCoords (coldChartSetting R V).free, (coldChartSetting R V).InBalls η → ∀ c : TorusBond n,
        1 / 2 ≤ meanNorm R.params ((coldChartSetting R V).field η) (coldChartSetting R V).bases c
end YangMills.Construction
end
