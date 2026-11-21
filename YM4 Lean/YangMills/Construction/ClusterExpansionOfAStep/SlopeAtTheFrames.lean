import YangMills.Construction.ClusterExpansionOfAStep.SizeOfADensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings StepCosts TorusFields
def FrameSlopeBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ (K : SettingCore R n) (Y : TorusSite n), s.IsCoreOf K → s.IsMarked K → s.AwayFromCore K Y →
        ∀ (b : s.free) (X : EuclideanSpace ℝ (Fin 3)), ‖X‖ = 1 →
          (16 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range →
          R.coupling * |deriv (fun τ : ℝ => s.totalCost (Function.update 0 b (τ • X))) 0| ≤ C
end YangMills.Construction.ClusterExpansionOfAStep
end
