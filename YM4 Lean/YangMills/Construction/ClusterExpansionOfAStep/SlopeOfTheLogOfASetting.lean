import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusFields
def LogJacobianSlopeBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ (b : s.free) (X : EuclideanSpace ℝ (Fin 3)), ‖X‖ = 1 →
        |deriv (fun τ : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (τ • X))) 0| ≤ C
end YangMills.Construction.ClusterExpansionOfAStep
end
