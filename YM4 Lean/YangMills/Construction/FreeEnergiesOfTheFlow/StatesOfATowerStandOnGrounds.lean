import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open StepGas TorusLumps StepSettings WeightedResponses
def TowerStatesAreGroundStates : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (top : ℕ),
    S.params = Kr →
    S.FollowsFlow β top → CouplingsAboveFloor (Tb.stepParameters y) β top → ∀ u < top,
      (T.stage u).toStepSetup.IsWellPosed ∧
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
        ∀ᵐ x ∂(markedSampleLaw T β (u + 1) n),
        (hotCaseGround (T.stage u).toStepSetup x.2.2.1 (stageState T (u + 1) n x).2).IsAdmissibleGround ∧
        IsLiveState (Tb.stepParameters y) (T.stage (u + 1)).coupling (T.stage (u + 1)).labelWeight x.2.2.1
          (stageState T (u + 1) n x).2.1 (stageState T (u + 1) n x).2.2
end YangMills.Construction.FreeEnergies
end
