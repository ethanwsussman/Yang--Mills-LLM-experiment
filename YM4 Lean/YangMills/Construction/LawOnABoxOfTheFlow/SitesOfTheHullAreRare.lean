import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents
open WeightedResponses ResponseInTheExpansion BoxGaussian TorusFields TorusLumps RenormalizationStepParameters
def hullSiteRareStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∃ y₂ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β k → T.MarksMeasurable → y₂ ≤ flowCoupling (Tb.stepParameters y) β k →
    (∃ e : ℕ, n = 2 * (Tb.stepParameters y).side ^ e) →
    2 * CellWindows.baseCellSide (Tb.stepParameters y).side (clusterRange (flowCoupling (Tb.stepParameters y) β k)) ≤ n →
    ∀ z : TorusSite n, (markedSampleLaw T β k n).real {u | z ∈ (stageState T k n u).2.1} ≤
      Real.exp (-(flowCoupling (Tb.stepParameters y) β k * Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5))
end YangMills.Construction.BoxEvents
end
