import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open TorusFields
def FreeComponentsAreClusterSupports : Prop :=
  ∀ (n L r : ℕ) [NeZero n] [NeZero L] (bad : Finset (TorusBond (n * L))) (Y : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) (X : Finset (TorusSite (n * L))),
    X ∈ clusterComponents L r bad Y C → Disjoint X (sitesInBlocks L C) →
      clusterSupportSites L (supportOfComponent L bad Y X) = X ∧
        IsClusterSupport L r (supportOfComponent L bad Y X)
end YangMills.Construction.TorusLumps
end
