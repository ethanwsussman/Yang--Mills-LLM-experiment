import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import YangMills.Construction.TransfersOffTheWalk.ProductsAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields TorusLumps StepSettings WeightedResponses FreeEnergies ResponseInTheExpansion ClusterExpansionOfAStep
def separatedProductsStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ p : ℕ, ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (s n : ℕ) [NeZero n] (D : ℕ → ℝ)
      (f : Fin p → FinePlaquetteFunction),
      S.params = Kr → S.FollowsFlow β s → CouplingsAboveFloor (Tb.stepParameters y) β s →
      IsBlockTorusSide (Tb.stepParameters y) n →
      (∀ i, weightNorm (Tb.stepParameters y).side s
        (fineWeight (f i) (fineSide (Tb.stepParameters y).side s n)) ≤ 1) →
      SeparatedAlongTower (Tb.stepParameters y) (flowCoupling (Tb.stepParameters y) β) D s n
        (fun i => fineWeight (f i) _) →
      HasConditionalMean T β s n (fun u => ∏ i, completedCentered S (f i) s n u) ∧
      ∀ᵐ u ∂(markedSampleLaw T β s n),
        |conditionalProduct S β f Finset.univ s n u - ∏ i, fittedResponse S (f i) s n (stageState T s n u)| ≤
          separationError (Tb.stepParameters y) Cp Kr.C₀ D s n (fun i => fineWeight (f i) _) *
            ∏ i, scoreMeanOver S (f i) s n (stageState T s n u)
end YangMills.Construction.TransfersOffTheWalk
end
