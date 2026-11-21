import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
open WeightedResponses ResponseInTheExpansion BoxGaussian TorusFields TorusLumps RenormalizationStepParameters
def plaquetteEnergyTailStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∃ C t₀ yP : ℝ, 0 < t₀ ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j n : ℕ) [NeZero n], IsTowerAtParameters Tb y T β j → T.MarksMeasurable →
      yP ≤ flowCoupling (Tb.stepParameters y) β j → 2 * (Tb.stepParameters y).side ∣ n →
      (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∀ t : ℝ, 0 < t → t ≤ t₀ →
        (markedSampleLaw T β j n).real {u | t < plaquetteEnergy (topField (Tb.stepParameters y) j n u) p.1 p.2.1 p.2.2} ≤
          Real.exp (C * Real.log (flowCoupling (Tb.stepParameters y) β j) -
            2 * Tb.coercivity * flowCoupling (Tb.stepParameters y) β j * t)
end YangMills.Construction.BoxEvents
end
