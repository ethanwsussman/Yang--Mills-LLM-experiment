import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages LumpContours TorusFields
variable {n : ℕ}
section AttachedSets
variable [NeZero n] (L : ℕ) [NeZero L]
def attachedInBlocks (r : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C X : Finset (TorusSite n)) : Finset (TorusSite (n * L)) :=
  open Classical in attachedSites L r bad Yt C ∩ sitesInBlocks L X
open Classical in
def componentsWithin (r : ℕ) (Yt K : Finset (TorusSite (n * L))) : Finset (TorusSite (n * L)) :=
  ((chainComponents r Yt).filter (· ⊆ K)).biUnion id
open Classical in
def badBlocksOff (bad : Finset (TorusBond (n * L))) (C : Finset (TorusSite n))
    (K : Finset (TorusSite (n * L))) : Finset (TorusSite n) :=
  ((bad.image Prod.fst ∩ K).image (parentBlock L)) \ C
end AttachedSets
def ImageUnionLengthBound : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (r r' : ℕ), 1 ≤ r → r ≤ r' + 1 → 2 ^ 16 ≤ r' →
    ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)) (bad : Finset (TorusBond (n * ℓ.side)))
      (Yt : Finset (TorusSite (n * ℓ.side))) (P : Finset (Finset (TorusSite n))),
      P ⊆ chainComponents r' (coarseHull ℓ.side r r' bad Yt (thickening (2 * r') (torusHotSites ℓ V))) →
      (excessLength ℓ r' (P.biUnion id) V : ℝ) ≤
        ((badBlocksOff ℓ.side bad (thickening (2 * r') (torusHotSites ℓ V))
            (attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V))
              (P.biUnion id))).card : ℝ) +
          40 / (ℓ.side : ℝ) *
            (((open Classical in (torusHotLumps ℓ W).filter
                (· ⊆ attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V))
                  (P.biUnion id))).card : ℝ) +
              (excessLength ℓ r (componentsWithin ℓ.side r Yt
                (attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V))
                  (P.biUnion id))) W : ℝ))
end TorusLumps
end YangMills.Construction
end
