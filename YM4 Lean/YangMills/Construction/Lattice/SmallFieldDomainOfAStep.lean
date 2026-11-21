import YangMills.Construction.Lattice.CubesOfAStep
import YangMills.Construction.Lattice.ScaleLabels
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
abbrev LabelAtLevel (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ) (k : ℕ) : Type :=
  ScaleLabel c.L m K (Nat.log c.L c.M)
    (fun j => Nat.log c.L (c.L * secondSize c * blockSizeAt c x j)) k
def incomingRegion : ∀ {k : ℕ}, LabelAtLevel c m K x k → Set (FourTorus c.L m)
  | 0, _ => ∅
  | k + 1, S => S.largeField ⟨k + 1, by simp⟩
def unionsOfTestCubes (k : ℕ) (R : Set (FourTorus c.L m)) : Set (Set (FourTorus c.L m)) :=
  {P | ∃ C ⊆ partitionCubesIn (testPartitionIndex c K x k) R, P = ⋃₀ C}
def partitionOfUnityTerm (L : ℕ) {m : ℕ} (i : ℤ) (f : Set (FourTorus L m) → ℝ)
    (R P : Set (FourTorus L m)) : ℝ :=
  (∏ᶠ Q ∈ partitionCubesIn i R \ partitionCubesIn i P, f Q) *
    ∏ᶠ Q ∈ partitionCubesIn i P, (1 - f Q)
def plaquetteTestRegion (k : ℕ) (Y : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  complementRegion (coarsePartitionIndex c K x k)
    (coarseCollar c K x k (coarseCubeHull c K x k Y) 4)
def plaquetteUnityTerm (k : ℕ) (V : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2)
    (R P : Set (FourTorus c.L m)) : ℝ :=
  partitionOfUnityTerm c.L (testPartitionIndex c K x k) (plaquetteIndicator c K x k V) R P
def gaugeFixedRegion (k : ℕ) (P W : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  ⋃₀ (partitionCubesIn (coarsePartitionIndex c K x k) (complementRegion (coarsePartitionIndex c K x k)
        (coarseCollar c K x k (coarseCubeHull c K x k P) 1)) ∩
      partitionCubesIn (coarsePartitionIndex c K x k)
        (complementRegion (coarsePartitionIndex c K x k) W))
def stepGaugeFixedRegion (k : ℕ) (P Y : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  gaugeFixedRegion c K x k P (coarseCollar c K x k (coarseCubeHull c K x k Y) 5)
def gaugeFixedSites (k : ℕ) (X : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (k + 1)) :=
  {y | ∀ z ∈ sitesInBlock (levelDepth K k) y, (z : FourTorus c.L m) ∈ X}
def fluctuationTestRegion (k : ℕ) (X : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  coarseCollar c K x k X (-1)
def fluctuationUnityTerm (k : ℕ) (Vk : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) (R Q : Set (FourTorus c.L m)) : ℝ :=
  partitionOfUnityTerm c.L (testPartitionIndex c K x k) (fluctuationIndicator c K x k Vk Vt) R Q
def smallFieldRegion (k : ℕ) (X Q : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  complementRegion (coarsePartitionIndex c K x k)
    (coarseCollar c K x k (coarseCubeHull c K x k Q) 2 ∪
      coarseCollar c K x k (complementRegion (coarsePartitionIndex c K x k) X) 3)
def initialDensityUnityTerm (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2)
    (P : Set (FourTorus c.L m)) : ℝ :=
  partitionOfUnityTerm c.L (densityPartitionIndex c K x 0) (densityCubeIndicator c K x 0 U) univ P
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
