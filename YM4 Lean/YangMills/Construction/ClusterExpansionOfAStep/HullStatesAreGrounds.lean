import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def HullStateIsHotCase : Prop :=
  ∀ T : ParameterAssignment, T.Admissible →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.IsWellPosed →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ (V : TorusField n) (q : CoarseState S n),
        IsHullState S.params S.nextRange V q.1 →
        (∀ X ∈ chainComponents S.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround S V q).IsHotCase
end YangMills.Construction.StepGas
end
