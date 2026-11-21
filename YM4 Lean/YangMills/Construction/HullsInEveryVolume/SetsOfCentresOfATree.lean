import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps WeightedResponses
def FewLeafSiteFamilies : Prop :=
  ∃ C₁ : ℕ → ℝ, EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y))
      (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
    ∃ F : TorusSite n → (j : ℕ) → Finset (Finset (TorusSite (fineSide (Tb.stepParameters y).side j n))),
      ∀ (z : TorusSite n) (j : ℕ), j ≤ u →
        ((F z j).card : ℝ) ≤ Real.exp (C₁ (Tb.stepParameters y).side * (minLeafCount (Tb.stepParameters y).side j : ℝ) *
          (1 + Real.log ((j : ℝ) + 1)) * (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log (stageCoupling T (u - j)))) ∧
        (∀ S ∈ F z j, S.card = minLeafCount (Tb.stepParameters y).side j) ∧
        ∀ (w : MarkedSample (Tb.stepParameters y) u n) (tr : SiteTree (Tb.stepParameters y).side u n), tr.root = z →
          tr.Embeds T (treeBranching (Tb.stepParameters y).side) w →
          levelWeight j * (treeBranching (Tb.stepParameters y).side : ℝ) ^ j ≤ (tr.leavesAtDepth j : ℝ) →
          ∃ S ∈ F z j, S ⊆ tr.leafSites j
end YangMills.Construction.HullTrees
end
