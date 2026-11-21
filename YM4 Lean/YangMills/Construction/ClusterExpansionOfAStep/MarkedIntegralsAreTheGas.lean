import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def MarkedIntegralEqPartition : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.IsSymmetricWeight → S.nextCoupling = S.coupling →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
        (∀ A : Finset (TorusSite n), S.markedIntegral A V =
          S.functional (n * S.params.side) (trivialField (n * S.params.side)) *
            ((coldCaseGround S V).partitionFunction A).toReal) ∧
        ∀ Y : TorusSite n, (coldCaseGround S V).blockDensity Y = S.blockDensity n Y V
end YangMills.Construction.StepGas
end
