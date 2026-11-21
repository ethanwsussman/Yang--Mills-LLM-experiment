import YangMills.Construction.HullsInEveryVolume.LocalHullOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def localHullSubsetStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb Kr y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)),
    (∀ (u n : ℕ) [NeZero n], HullTrees.HullChainAtLevel Tb y g β K m T u n →
      ∀ w : WeightedResponses.MarkedSample (Tb.stepParameters y) u n,
      (∀ Q : Finset (TorusFields.TorusSite n),
        (HullTrees.localHullData T Kr.s₁ u n w Q).1 ⊆ HullTrees.hullSet T u n w ∧
        ∀ z ∈ (HullTrees.localHullData T Kr.s₁ u n w Q).1,
          (HullTrees.localHullData T Kr.s₁ u n w Q).2 z ≤ HullTrees.siteSize T Kr.s₁ u n w z) ∧
      ∀ (z : TorusFields.TorusSite n) (D : ℝ), 0 < D → z ∈ HullTrees.hullSet T u n w →
        ((HullTrees.supDiam (HullTrees.hullClass (HullTrees.stageRange T u) (HullTrees.hullSet T u n w) z) : ℕ) : ℝ) < D →
        z ∈ (HullTrees.localHullData T Kr.s₁ u n w (HullTrees.localHullBox T u z D)).1 ∧
          (HullTrees.localHullData T Kr.s₁ u n w (HullTrees.localHullBox T u z D)).2 z =
            HullTrees.siteSize T Kr.s₁ u n w z) ∧
    ∀ (j n : ℕ) [NeZero n], HullTrees.HullChainAtLevel Tb y g β K m T (j + 1) n →
      ∀ (w : WeightedResponses.MarkedSample (Tb.stepParameters y) (j + 1) n) (Q : Finset (TorusFields.TorusSite n)),
        HullTrees.localCoreZone T Kr.s₁ j n w Q ⊆ HullTrees.coreZone T j n w
end YangMills.Construction.HullTrees
end
