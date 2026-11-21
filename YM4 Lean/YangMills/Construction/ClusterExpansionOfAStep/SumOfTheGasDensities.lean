import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def LogPartitionEqSumDensities : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.nextCoupling ≤ 1.01 * S.coupling → ∀ (n : ℕ) [NeZero n]
      (G : GasGround S n), G.IsAdmissibleGround →
      Real.log (G.xi ∅) = ∑ Y : TorusSite n, G.blockDensity Y ∧
        ∀ Y : TorusSite n, 0 ≤ G.blockDensity Y ∧ G.blockDensity Y ≤ Real.exp (-(6 * T.gasRate * S.coupling))
end YangMills.Construction.StepGas
end
