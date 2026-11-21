import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepReturn
open RenormalizationStepParameters
def ExpansionHoldsAtAdmissibleParameters : Prop :=
  ∃ (sideMin : ℝ → ℕ) (rtMax : ChainParameters → ℝ) (thresholdMax : ChainParameters → ℝ → ℝ)
    (sizeMin : ChainParameters → ℝ → ℝ → ℕ) (csMin : ChainParameters → ℝ → ℝ → ℝ),
    (∀ P, 0 < rtMax P) ∧ (∀ P r, 0 < thresholdMax P r) ∧
      ∀ T : ParameterAssignment, T.Admissible → sideMin T.coupling ≤ T.side → T.rt ≤ rtMax T.toChainParameters →
        T.threshold ≤ thresholdMax T.toChainParameters T.rt →
        sizeMin T.toChainParameters T.rt T.threshold ≤ T.n₀ →
        csMin T.toChainParameters T.rt T.threshold ≤ T.Cs → T.ColdStepHolds →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionReturnsAt (T.stepParameters y)
end YangMills.Construction.StepReturn
end
