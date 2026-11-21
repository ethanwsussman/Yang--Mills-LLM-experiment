import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def conditionalProductMeansStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ (β : ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y))
    (S : ScoredStageTower T) (tp : ℕ), S.params = Kr →
    S.FollowsFlow β tp → CouplingsAboveFloor (Tb.stepParameters y) β tp →
    ∀ (k : ℕ) (f : Fin k → FinePlaquetteFunction) (I : Finset (Fin k)) (n : ℕ) [NeZero n],
      TorusLumps.IsBlockTorusSide (Tb.stepParameters y) n →
      (∀ s : ℕ, HasConditionalMean T β s n (fun u => ∏ i ∈ I, completedCentered S (f i) s n u)) ∧
      ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β 0 n),
        conditionalProduct S β f I 0 n u = ∏ i ∈ I, fittedResponse S (f i) 0 n (WeightedResponses.stageState T 0 n u)
end YangMills.Construction.FreeEnergies
end
