import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def sampleBelowLawStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y =>
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k s n : ℕ) [NeZero n],
    ResponseInTheExpansion.IsTowerAtParameters Tb y T β (k + s) → T.MarksMeasurable →
    (∀ j ≤ k + s, y ≤ flowCoupling (Tb.stepParameters y) β j) →
    IsProbabilityMeasure (WeightedResponses.markedSampleLaw T β (k + s) n) ∧
      (WeightedResponses.markedSampleLaw T β (k + s) n).map
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) k s n) =
        WeightedResponses.markedSampleLaw T β k (WeightedResponses.fineSide (Tb.stepParameters y).side s n)
end YangMills.Construction.BoxEvents
end
