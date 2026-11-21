import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters TorusFields
def LogJacobianLeLog : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ η : FreeCoords s.free, s.InBalls η → ∀ Y : TorusSite n,
        |s.logJacobian (s.field η) η Y| ≤ C * Real.log R.coupling
end YangMills.Construction.ClusterExpansionOfAStep
end
