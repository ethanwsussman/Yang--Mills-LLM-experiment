import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings RenormalizationStepParameters StepCosts
def LevelShareBounded : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ A : ℝ, 0 < A ∧ ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y →
    R.params = T.stepParameters y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible → ∀ Y : TorusSite n,
      0 ≤ levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse ∧
        levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse ≤ A
end YangMills.Construction.ClusterExpansionOfAStep
end
