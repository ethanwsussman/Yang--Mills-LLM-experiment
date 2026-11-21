import YangMills.Construction.ClusterExpansionOfAStep.SizeOfADensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings StepCosts TorusFields
def FrameCostNearLevelShare : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C c y₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ (K : SettingCore R n) (Y : TorusSite n), s.IsCoreOf K → s.IsMarked K → s.AwayFromCore K Y →
        |s.blockCostAt Y 0 - levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse| ≤
          R.coupling ^ C * Real.exp (-c * (R.range : ℝ))
end YangMills.Construction.ClusterExpansionOfAStep
end
