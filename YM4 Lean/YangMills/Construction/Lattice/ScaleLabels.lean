import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsScaledCubeUnion (K k n : ℕ) (X : Set (FourTorus L m)) : Prop :=
  n + k ≤ m + K ∧ IsPartitionRegion (scaledCubeIndex K k n) X
def regionDiff (i : ℤ) (X Y : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ (partitionCubesIn i X \ partitionCubesIn i Y)
abbrev ScaleIndex (k : ℕ) : Type := Set.Icc 1 k
@[ext]
structure ScaleData (L m : ℕ) where
  domain : Set (FourTorus L m)
  smallFieldRegion : Set (FourTorus L m)
  markedSet : Set (FourTorus L m)
@[ext]
structure ScaleLabel (L m K m' : ℕ) (c : ℕ → ℕ) (k : ℕ) where
  atScale : ScaleIndex k → ScaleData L m
  level_le : k ≤ K
  domain_isUnion : ∀ j : ScaleIndex k, IsScaledCubeUnion K j m' (atScale j).domain
  smallFieldRegion_isUnion : ∀ j : ScaleIndex k,
    IsScaledCubeUnion K j m' (atScale j).smallFieldRegion
  smallFieldRegion_subset_domain : ∀ j : ScaleIndex k,
    (atScale j).smallFieldRegion ⊆ (atScale j).domain
  succ_domain_subset : ∀ j j' : ScaleIndex k, (j' : ℕ) = j + 1 →
    (atScale j').domain ⊆ (atScale j).smallFieldRegion
  markedSet_subset : ∀ j : ScaleIndex k, (atScale j).markedSet ⊆
    regionDiff (coarseCubeIndex K m' j) (atScale j).domain (atScale j).smallFieldRegion
  markedSet_empty_or_union : ∀ j : ScaleIndex k,
    (atScale j).markedSet = ∅ ∨ IsScaledCubeUnion K j (c j) (atScale j).markedSet
namespace ScaleLabel
variable {K m' k : ℕ} {c : ℕ → ℕ}
def domainSeq (S : ScaleLabel L m K m' c k) (j : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if h : j ∈ Set.Icc 1 k then (S.atScale ⟨j, h⟩).domain else univ
def largeField (S : ScaleLabel L m K m' c k) (j : ScaleIndex k) : Set (FourTorus L m) :=
  complementRegion (coarseCubeIndex K m' j) (S.atScale j).smallFieldRegion
def largeFieldParts (S : ScaleLabel L m K m' c k) (j : ScaleIndex k) :
    Set (Set (FourTorus L m)) :=
  regionComponents (coarseCubeIndex K m' j) (S.largeField j)
end ScaleLabel
end YangMills.Construction.PeriodicLattice
