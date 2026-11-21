import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open RenormalizationStepParameters TorusFields TorusLumps
def ColdImageFactorsThroughColdStep : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ S : StepSetup, S.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ U : TorusField n, IsCold (9 / 8 * T.threshold) U →
      coldImageIntegral S U = S.functional (n * S.params.side) (trivialField _) * coldStepIntegral S n U ∧
      ∀ Y : TorusSite n, coldLocalDensity S T.lam n Y U =
        coldInteractionDensity S T.lam n Y U + coldExpansionDensity S n Y U + coldFrameDensity S n Y U
end YangMills.Construction.StepSettings
end
