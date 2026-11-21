import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def CoarseFactorExpansionMeasurable : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.IsWellPosed →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ Y : Finset (TorusSite n),
      ∀ X : Finset (TorusSite n),
        Measurable fun p : TorusField n × (Y → CoarseLabel S.labels.Ω S.params.side) => coarseFactorExpansion S n p.1 Y p.2 X
end YangMills.Construction.StepGas
end
