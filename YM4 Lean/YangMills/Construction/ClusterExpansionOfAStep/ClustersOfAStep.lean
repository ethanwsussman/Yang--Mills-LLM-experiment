import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open TorusFields (TorusField TorusBond TorusSite)
def CoarseHullIsHullState : Prop :=
  ∀ (P : StepParameters), P.Admissible → ∀ (r r' : ℕ), r ≤ r' + 1 → 2 ^ 16 ≤ r' → ∀ (n : ℕ) [NeZero n], P.side ∣ n →
    ∀ (V : TorusField n) (bad : Finset (TorusBond (n * P.side))) (Y : Finset (TorusSite (n * P.side))),
      IsHullState P r' V (coarseHull P.side r r' bad Y (thickening (2 * r') (torusHotSites P V)))
end YangMills.Construction.TorusLumps
end
