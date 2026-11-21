import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin RenormalizationStepParameters StepSettings StepGas
def GasConfigIsAdmissibleSetting : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ σ : G.Config,
      G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible
end YangMills.Construction.ClusterExpansionOfAStep
end
