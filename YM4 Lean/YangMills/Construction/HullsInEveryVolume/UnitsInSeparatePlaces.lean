import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def separatedUnitsBoundStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel Tb y g β K m T u n →
    ∀ S : Finset (TorusFields.TorusSite n), HullTrees.Separated (30 * HullTrees.stageRange T u) S →
      (WeightedResponses.markedSampleLaw T β u n).real {w | ∀ z ∈ S, HullTrees.IsUnit T u n w z} ≤
        Real.exp (-(HullTrees.separatedUnitRate Tb * HullTrees.stageCoupling T u * (S.card : ℝ)))
end YangMills.Construction.HullTrees
end
