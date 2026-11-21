import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open RenormalizationStepParameters TorusFields
def coldImageIntegral_eq_on_small_torus : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → n ≤ 4 * R.frameReach + 5 → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      coldImageIntegral R V = R.functional (n * R.params.side) (trivialField _) * coldStepIntegral R n V
end YangMills.Construction.StepSettings
end
