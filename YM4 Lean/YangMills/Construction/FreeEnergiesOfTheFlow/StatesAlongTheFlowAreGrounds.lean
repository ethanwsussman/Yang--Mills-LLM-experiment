import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusLumps TorusFields StepGas StepSettings WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep
def flowStatesAreGroundsStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y))
    (S : ScoredStageTower T) (tp : ℕ),
    S.params = Kr → S.FollowsFlow β tp → CouplingsAboveFloor (Tb.stepParameters y) β tp →
    (∀ u < tp, (T.stage u).toStepSetup.IsWellPosed ∧
      |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B) ∧
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      (∀ w ≤ tp, ∀ᵐ d ∂(markedSampleLaw T β w n),
        IsLiveState (Tb.stepParameters y) (T.stage w).coupling (T.stage w).labelWeight
          (stageState T w n d).1 (stageState T w n d).2.1 (stageState T w n d).2.2) ∧
      ∀ u < tp, ∀ᵐ d ∂(markedSampleLaw T β (u + 1) n),
        (hotCaseGround (T.stage u).toStepSetup d.2.2.1 (stageState T (u + 1) n d).2).IsAdmissibleGround
end YangMills.Construction.FreeEnergies
end
