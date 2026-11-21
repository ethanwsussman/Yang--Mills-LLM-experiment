import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses
open InfiniteLattice (AmbientSpace)
def unitTorusWeightSizesStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ K k : ℕ, k ≤ K → ∀ (d vt : ℝ) (c : AmbientSpace) (g : AmbientSpace → ℝ),
    0 < d → d < 1 / 2 → 0 < vt →
    (∀ x, |g x| ≤ 1) → (∀ x x', |g x - g x'| ≤ TorusMetric.euclidNormVec (x - x') / (vt * d)) →
    (∀ x, g x ≠ 0 → TorusMetric.euclidNormVec (x - c) ≤ d) →
    weightSup (unitTorusWeight L K k g) ≤ 1 ∧
    weightLipschitz L k (unitTorusWeight L K k g) ≤ 2 / (vt * lengthInSites L K k d) ∧
    ((ResponseInTheExpansion.weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k g)).card : ℝ) ≤
      (4 * lengthInSites L K k d + 11) ^ 4
end YangMills.Construction.StateLaws
end
