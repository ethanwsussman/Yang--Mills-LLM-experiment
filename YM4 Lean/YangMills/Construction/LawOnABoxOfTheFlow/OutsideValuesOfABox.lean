import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters TorusLumps BoxEvents BlockAverages WeightedResponses ResponseInTheExpansion
def outerDataOfSample {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k s n : ℕ) [NeZero n]
    (o : TorusSite (fineSide ℓ.side s n)) (R : ℕ) (u : MarkedSample ℓ (k + s) n) : OuterData T k o R :=
  outerData T k o R (stageState T k _ (sampleBelow ℓ k s n u))
def goodOuterDataStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ (xs : ℝ) (xp : ℕ → ℝ),
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k s n : ℕ) [NeZero n]
      (o : TorusSite (fineSide (Tb.stepParameters y).side s n)) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xs k (fineSide (Tb.stepParameters y).side s n) → x = flowCoupling (Tb.stepParameters y) β k →
      R = boxRadius κ₀ x → s = coarseningSteps (Tb.stepParameters y).side R →
      ∃ H : Set (OuterData T k o R), MeasurableSet H ∧ (∀ q ∈ H, Disjoint q.2.1 (supBall o (3 * R))) ∧
        (∀ p : ℕ, xp p ≤ x → 1 - x ^ (-(p : ℝ)) ≤
          (markedSampleLaw T β (k + s) n).real {u | outerDataOfSample T k s n o R u ∈ H}) ∧
        ∀ B : Set (OuterData T k o R), MeasurableSet B → B ⊆ H →
          11 / 16 * (markedSampleLaw T β (k + s) n).real {u | outerDataOfSample T k s n o R u ∈ B} ≤
            (markedSampleLaw T β (k + s) n).real {u | outerDataOfSample T k s n o R u ∈ B ∧
              IsColdOnBox o R (boxScale x) (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).1
                (stageState T k _ (sampleBelow (Tb.stepParameters y) k s n u)).2.1 ∧
              IsGoodSample (Tb.stepParameters y) k s (apexRadius (Tb.stepParameters y).side s R) (boxScale x)
                (Real.log x ^ 2 / x) s n u o}
end YangMills.Construction.BoxGaussian
end
