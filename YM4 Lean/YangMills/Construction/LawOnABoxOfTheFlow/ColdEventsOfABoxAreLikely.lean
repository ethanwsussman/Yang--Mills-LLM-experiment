import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def coldEventsLikelyStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∃ (xs : ℝ) (xp : ℕ → ℝ),
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k s n : ℕ) [NeZero n]
      (o : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side s n)) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xs k (WeightedResponses.fineSide (Tb.stepParameters y).side s n) →
      x = flowCoupling (Tb.stepParameters y) β k →
      R = BoxGaussian.boxRadius κ₀ x → s = BoxGaussian.coarseningSteps (Tb.stepParameters y).side R →
      ∀ p : ℕ, xp p ≤ x →
        (WeightedResponses.markedSampleLaw T β k
            (WeightedResponses.fineSide (Tb.stepParameters y).side s n)).real
            {ω | ¬ IsColdOnBox o R (BoxGaussian.boxScale x) (WeightedResponses.stageState T k _ ω).1
              (WeightedResponses.stageState T k _ ω).2.1} ≤
          x ^ (-(p : ℝ)) ∧
        (WeightedResponses.markedSampleLaw T β (k + s) n).real
            {ω | ¬ IsGoodSample (Tb.stepParameters y) k s (apexRadius (Tb.stepParameters y).side s R)
              (BoxGaussian.boxScale x) (Real.log x ^ 2 / x) s n ω o} ≤ x ^ (-(p : ℝ))
end YangMills.Construction.BoxEvents
end
