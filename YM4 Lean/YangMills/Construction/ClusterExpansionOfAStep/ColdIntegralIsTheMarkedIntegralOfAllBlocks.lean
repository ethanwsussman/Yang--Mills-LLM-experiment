import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
def FullMarkedIntegralIsColdImage : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.IsSymmetricWeight →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold (9 / 8 * T.threshold) V →
      R.markedIntegral Finset.univ V = coldImageIntegral R V
end YangMills.Construction.StepSettings
end
