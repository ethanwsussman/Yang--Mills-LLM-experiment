import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfAGround
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open StepGas StepSettings RenormalizationStepParameters
def SettingAdmissibleOfHasWeight : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ γ : GasFamily R n, G.IsGasFamily γ → ∀ η, G.HasWeightAt γ η → (G.settingOf γ).IsAdmissible
end ClusterExpansionOfAStep
end YangMills.Construction
end
