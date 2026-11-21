import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps
def AttachedUnchangedByFarSets : Prop :=
  ∀ (n L : ℕ) [NeZero n] [NeZero L] (r : ℕ) (bad Δb : Finset (TorusBond (n * L)))
    (Yt ΔY : Finset (TorusSite (n * L))) (C : Finset (TorusSite n)),
    (open Classical in bad.image Prod.fst ∪ Yt ⊆ attachedSites L r bad Yt C) →
    (open Classical in ∀ z ∈ Δb.image Prod.fst ∪ ΔY, ∀ u ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C,
      10 * r < supDist z u) →
    (open Classical in attachedSites L r (bad ∪ Δb) (Yt ∪ ΔY) C = bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C)
end YangMills.Construction.ClusterExpansionOfAStep
end
