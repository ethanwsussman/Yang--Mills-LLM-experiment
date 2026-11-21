import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
def StepParameters.RangeFloor (ℓ : StepParameters) (c : ℝ) : Prop :=
  ∀ x : ℝ, ℓ.y₁ ≤ x → ℓ.side ≤ clusterRange x ∧ (2 ^ 16 + 2 ^ 7 * ℓ.rt) * (clusterRange x : ℝ) ^ 4 ≤ c * x
variable {n : ℕ}
abbrev ClusterSupport (L n : ℕ) : Type := Finset (TorusBond (n * L)) × Finset (TorusSite (n * L))
section Supports
variable [NeZero n] (L : ℕ) [NeZero L]
open Classical in
def clusterSupportSites (θ : ClusterSupport L n) : Finset (TorusSite (n * L)) := θ.1.image Prod.fst ∪ θ.2
def IsClusterSupport (r : ℕ) (θ : ClusterSupport L n) : Prop :=
  (clusterSupportSites L θ).Nonempty ∧
    ∀ y ∈ clusterSupportSites L θ, ∀ z ∈ clusterSupportSites L θ,
      ChainConnected (10 * r) (clusterSupportSites L θ) y z
open Classical in
def badBlockCount (θ : ClusterSupport L n) : ℕ := (θ.1.image fun b => parentBlock L b.1).card
def supportUnitCount (r : ℕ) (θ : ClusterSupport L n) : ℕ :=
  badBlockCount L θ + ballCoverNumber (4 * r) θ.2
def clusterWeight (c x : ℝ) (r : ℕ) (θ : ClusterSupport L n) : ℝ :=
  Real.exp (-(16 * c * x * (supportUnitCount L r θ : ℝ)))
def supportCore (r : ℕ) (θ : ClusterSupport L n) : Finset (TorusSite n) :=
  coreBlocks L r (clusterSupportSites L θ)
def siteDiameter (S : Finset (TorusSite n)) : ℕ := S.sup fun y => S.sup fun z => supDist y z
open Classical in
def supportsAtBlock (r : ℕ) (Y : TorusSite n) : Finset (ClusterSupport L n) :=
  Finset.univ.filter fun θ => IsClusterSupport L r θ ∧ Y ∈ supportCore L r θ
open Classical in
def supportOfComponent (bad : Finset (TorusBond (n * L))) (Yt X : Finset (TorusSite (n * L))) :
    ClusterSupport L n :=
  (bad.filter fun b => b.1 ∈ X, Yt ∩ X)
end Supports
end YangMills.Construction.TorusLumps
end
