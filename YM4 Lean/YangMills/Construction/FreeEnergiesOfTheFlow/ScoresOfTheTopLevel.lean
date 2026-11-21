import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open RenormalizationStepParameters TorusLumps ClusterExpansionOfAStep WeightedResponses
def topLevelScoreBoundStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y))
    (S : ScoredStageTower T) (tp n : ℕ) [NeZero n], S.params = Kr → S.FollowsFlow β tp →
    CouplingsAboveFloor (Tb.stepParameters y) β tp → IsBlockTorusSide (Tb.stepParameters y) n →
      Integrable (fun u => Real.exp (S.totalScore tp n u)) (markedSampleLaw T β tp n) ∧
      1 ≤ S.expScoreMean β tp n ∧
      S.expScoreMean β tp n ≤
        Real.exp (C * (1 + Real.log (flowCoupling (Tb.stepParameters y) β tp)) * (n : ℝ) ^ 4)
end YangMills.Construction.FreeEnergies
end
