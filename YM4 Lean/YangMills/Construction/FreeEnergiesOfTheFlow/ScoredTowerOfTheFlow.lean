import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open RenormalizationStepParameters TorusLumps ClusterExpansionOfAStep WeightedResponses
def scoredTowerExistsStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ Tb : ParameterAssignment, Tb.coupling = a → Tb.side = L → Tb.Admissible → Tb.ColdStepHolds →
      Tb.HoldsFrom ColdRegimeEstimatesAt → Tb.rt ≤ rt₀ Tb.toChainParameters → C₀ ≤ Tb.derivBound →
      ∃ Kr : ResponseParameters, ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ExpansionHolds (Tb.stepParameters y) → ∀ (β : ℝ) (tp : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β tp →
        ∃ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T), S.params = Kr ∧ S.FollowsFlow β tp
end YangMills.Construction.FreeEnergies
end
