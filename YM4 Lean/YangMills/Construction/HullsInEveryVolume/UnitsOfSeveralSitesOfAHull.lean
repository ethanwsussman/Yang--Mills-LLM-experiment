import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps WeightedResponses
def UnitsOfSeparatedHullSites : Prop :=
  ∃ C₁ : ℕ → ℝ, EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y))
      (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
    ∀ mm : ℕ, 1 ≤ mm → ∃ F : (Fin mm → TorusSite n) → (j : ℕ) →
        Finset (Finset (TorusSite (fineSide (Tb.stepParameters y).side j n))),
      ∀ ys : Fin mm → TorusSite n, (∀ i i', i ≠ i' → 40 * stageRange T u ≤ supDist (ys i) (ys i')) →
        (∀ j ≤ u, ((F ys j).card : ℝ) ≤ 2 ^ mm * Real.exp (C₁ (Tb.stepParameters y).side *
            (minLeafCountScaled (Tb.stepParameters y).side j mm : ℝ) *
            (1 + Real.log ((j : ℝ) + 1)) * (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log (stageCoupling T (u - j)))) ∧
          ∀ S ∈ F ys j, S.card = minLeafCountScaled (Tb.stepParameters y).side j mm) ∧
        ∀ w : MarkedSample (Tb.stepParameters y) u n, (∀ i, ys i ∈ hullSet T u n w) →
          ∃ j ≤ u, ∃ S ∈ F ys j, UnitsAtDepth T j u n w S ∧ Separated (30 * stageRange T (u - j)) S
end YangMills.Construction.HullTrees
end
