import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.TransfersOffTheWalk.ProductsAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedObservables
open RenormalizationStepParameters TorusLumps TorusFields WeightedResponses FreeEnergies ClusterExpansionOfAStep ResponseInTheExpansion TransfersOffTheWalk
def majorantMomentsStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y))
    (S : ScoredStageTower T) (t k n : ℕ) [NeZero n]
    (B : Fin p → Finset (TorusSite (sideBelow (Tb.stepParameters y).side k n))),
    S.params = Kr → S.FollowsFlow β (t + k) → CouplingsAboveFloor (Tb.stepParameters y) β (t + k) →
    IsBlockTorusSide (Tb.stepParameters y) n → (∀ i, (B i).Nonempty) →
    Integrable (fun u => ∏ i, meanSiteScore (S.setup t).score (B i) (stageState T t _ u).2.1 (stageState T t _ u).2.2)
        (markedSampleLaw T β t (sideBelow (Tb.stepParameters y).side k n)) ∧
      ∫ u, ∏ i, meanSiteScore (S.setup t).score (B i) (stageState T t _ u).2.1 (stageState T t _ u).2.2
          ∂(markedSampleLaw T β t (sideBelow (Tb.stepParameters y).side k n)) ≤
        C * Real.exp (C * (1 + Real.log (flowCoupling (Tb.stepParameters y) β (t + k))) * (n : ℝ) ^ 4)
end YangMills.Construction.WeightedObservables
end
