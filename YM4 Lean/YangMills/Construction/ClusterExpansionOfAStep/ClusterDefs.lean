import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.LumpContours
variable {n : ℕ}
section Clusters
variable [NeZero n] (L : ℕ) [NeZero L]
open Classical in
def clusterComponents (r : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) : Finset (Finset (TorusSite (n * L))) :=
  chainComponents (10 * r) (bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C)
open Classical in
def attachedSites (r : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) : Finset (TorusSite (n * L)) :=
  ((clusterComponents L r bad Yt C).filter fun X => (X ∩ sitesInBlocks L C).Nonempty).biUnion id
open Classical in
def coreBlocks (r : ℕ) (θ : Finset (TorusSite (n * L))) : Finset (TorusSite n) :=
  Finset.univ.filter fun y => (sitesInBlocks L {y} ∩ thickening (4 * r) θ).Nonempty
open Classical in
def storedBlocks (r : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) : Finset (TorusSite n) :=
  C ∪ coreBlocks L r (attachedSites L r bad Yt C)
def coarseHull (r r' : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) : Finset (TorusSite n) :=
  thickening (r' / 2) (storedBlocks L r bad Yt C)
end Clusters
end YangMills.Construction.TorusLumps
end
