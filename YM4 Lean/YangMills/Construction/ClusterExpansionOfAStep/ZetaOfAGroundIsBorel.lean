import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas
def GroundBlockActivityMeasurable : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (Y : Finset (TorusSite n)) (y' : TorusSite n),
      open Classical in
      Measurable fun q : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
        if IsHullState R.params R.nextRange q.1 Y ∧ ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n q.1 Y q.2 X ≠ 0
        then (hotCaseGround R q.1 ⟨Y, q.2⟩).groundSetting.blockActivity T.lam y' else 0
end ClusterExpansionOfAStep
end YangMills.Construction
end
