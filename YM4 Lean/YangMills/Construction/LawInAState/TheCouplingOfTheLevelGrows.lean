import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters ResponseInTheExpansion
def couplingAtSeparation_tendsto_statement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Xi : ℝ, (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Xi →
    ∀ X : ℝ, ∃ d₁ : ℝ, 0 < d₁ ∧
    ∀ d : ℝ, 0 < d → d ≤ d₁ → ∀ (K : ℕ) (β : ℝ), IsFlowDatum (Tb.stepParameters y) Xi K β →
      minimalCutoff (Tb.stepParameters y) Xi d ≤ K → X ≤ couplingAtSeparation (Tb.stepParameters y) β K d
end YangMills.Construction.StateLaws
end
