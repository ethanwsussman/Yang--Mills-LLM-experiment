import YangMills.Construction.CellOfTheFlow.TheStepGivenItsStateIsTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def drawsStandOnGroundsStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y =>
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (j : ℕ),
      IsTowerAtParametersMeasurable Tb y T β (j + 1) →
      ∀ (m : ℕ) [NeZero m], TorusLumps.IsBlockTorusSide (Tb.stepParameters y) m →
        ∀ᵐ v ∂(WeightedResponses.markedSampleLaw T β (j + 1) m), (stageGround T j m v).IsAdmissibleGround
end YangMills.Construction.CellWindows
end
