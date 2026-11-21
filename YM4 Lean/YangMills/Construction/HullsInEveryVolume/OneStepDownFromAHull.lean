import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps WeightedResponses
def UnitOrSeparatedChildren : Prop :=
  EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T u n →
    ∀ (w : MarkedSample (Tb.stepParameters y) u n) (z : TorusSite n), z ∈ hullSet T u n w →
      IsUnit T u n w z ∨ HasSeparatedChildren T (treeBranching (Tb.stepParameters y).side) u n w z
end YangMills.Construction.HullTrees
end
