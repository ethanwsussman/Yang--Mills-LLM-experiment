import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def CoarseWeightExpansionMeasurable : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.IsWellPosed →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ Y : Finset (TorusSite n),
      open Classical in
      Measurable fun p : TorusField n × (Y → CoarseLabel S.labels.Ω S.params.side) =>
        if IsHullState S.params S.nextRange p.1 Y then coarseWeightExpansion S n p.1 Y p.2 else 0
end YangMills.Construction.StepGas
end
