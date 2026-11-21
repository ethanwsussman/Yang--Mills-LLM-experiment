import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def HasBaseChoices (θ : TorusLumps.StepParameters) (k : ℕ) :
    (d n : ℕ) → [NeZero n] → WeightedResponses.MarkedSample θ (k + d) n → Prop
  | 0, _, _, _ => True
  | d + 1, n, _, ω =>
    ω.2.1 ∈ TorusLumps.baseChoices θ
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame θ.side n) 0
          (WeightedResponses.topField θ (k + d) (n * θ.side) ω.1)) ∧
      HasBaseChoices θ k d (n * θ.side) ω.1
def circulationBoundStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∀ C₀ : ℝ, 0 < C₀ → ∃ xs : ℝ,
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k s n : ℕ) [NeZero n]
      (o : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side s n)) (x : ℝ) (R : ℕ)
      (A ζ : TorusFields.TorusBond (WeightedResponses.fineSide (Tb.stepParameters y).side s n) →
        BlockAverages.imaginaryQuaternions)
      (g : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side s n) →
        BlockAverages.UnitQuaternion)
      (ω : WeightedResponses.MarkedSample (Tb.stepParameters y) (k + s) n),
      IsBoxDatum Tb y T β κ₀ xs k (WeightedResponses.fineSide (Tb.stepParameters y).side s n) →
      x = flowCoupling (Tb.stepParameters y) β k →
      R = BoxGaussian.boxRadius κ₀ x → s = BoxGaussian.coarseningSteps (Tb.stepParameters y).side R →
      BoxGaussian.IsAxialSmall o R (BoxGaussian.boxScale x) A →
      ζ ∈ BoxGaussian.sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * BoxGaussian.boxScale x ^ 2) →
      BoxGaussian.IsInChart (ResponseInTheExpansion.supBall o (2 * R)) A ζ
        (TorusFields.gaugeTransform g (WeightedResponses.topField (Tb.stepParameters y) k _
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) k s n ω))) →
      (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
        TorusFields.curvature (WeightedResponses.topField (Tb.stepParameters y) k _
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) k s n ω)) p.1 p.2.1 p.2.2 ≤
          BoxGaussian.boxScale x) →
      IsGoodSample (Tb.stepParameters y) k s (apexRadius (Tb.stepParameters y).side s R)
        (BoxGaussian.boxScale x) (Real.log x ^ 2 / x) s n ω o →
      HasBaseChoices (Tb.stepParameters y) k s n ω →
      ∀ P ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
        ((Tb.stepParameters y).side : ℝ) ^ s *
            TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove (Tb.stepParameters y).side s n o) ≤
          (R : ℝ) / 8 + 2 * ((Tb.stepParameters y).side : ℝ) ^ s →
        ‖∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite
              (WeightedResponses.fineSide (Tb.stepParameters y).side s n))),
            blockWeight (Tb.stepParameters y).side s P p • ResponseInTheExpansion.lieFormCurl (A + ζ) p‖ ≤
          12 * ((Tb.stepParameters y).side : ℝ) ^ s * BoxGaussian.boxScale x
end YangMills.Construction.BoxEvents
end
