import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def hullClassDiameterTailStatement : Prop :=
  EventuallyInParameters fun P _ y => ∀ (g β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (P.stepParameters y))
    (u n : ℕ) [NeZero n], HullChainAtLevel P y g β K m T u n →
    ∀ (z : TorusFields.TorusSite n) (D : ℝ), 0 ≤ D →
      (WeightedResponses.markedSampleLaw T β u n).real {w | z ∈ hullSet T u n w ∧
          D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℝ)} ≤
        Real.exp (-(hullDecayRate P * stageCoupling T u * (1 + D / (stageRange T u : ℝ))))
end YangMills.Construction.HullTrees
end
