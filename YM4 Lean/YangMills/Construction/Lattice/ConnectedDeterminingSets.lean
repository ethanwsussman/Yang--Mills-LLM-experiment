import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.ScaleLabels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def nextMember (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (l : ℕ) : Set (FourTorus L m) :=
  if l < k then Ω (l + 1) else ∅
def cubeMeet (K : ℕ) (X Y : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ (partitionCubesIn (levelDepth K 0) X ∩ partitionCubesIn (levelDepth K 0) Y)
def doubleInterior (K n j : ℕ) (W : Set (FourTorus L m)) : Set (FourTorus L m) :=
  layerEnlargement (scaledCubeIndex K j n) W (-2)
def IsGluableRegion (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m)) :
    Prop :=
  IsActiveSetSetting K k Ω ∧ j ≤ k ∧ IsScaledCubeUnion K j n W ∧ W ⊆ Ω 0 ∧
    cubeMeet K W (nextMember k Ω j) ⊆ doubleInterior K n j W ∧
    W ⊆ Ω j ∪ doubleInterior K n j W
def cubeDiff (i : ℤ) (A B : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ partitionCubesIn i A ∧ ¬Q ⊆ B}
def gluedChain (K n j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m)) (i : ℕ) :
    Set (FourTorus L m) :=
  if i ≤ j then
    cubeMeet K (Ω i) (doubleInterior K n j W) ∪
      cubeDiff (scaledCubeIndex K i n) (shrinkingTower K n 0 W i) (doubleInterior K n j W)
  else cubeMeet K (Ω i) (doubleInterior K n j W)
def gluedActiveSet (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m)) :
    Set (Σ q : ℕ, BondAtLevel L m K q) :=
  activeBondSet K k (gluedChain K n j Ω W)
def gluedBoundaryData (K k j : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) (i : ℕ) :
    BondAtLevel L m K i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ activeBondsAt K k Ω i then V i b
    else familyMemberLift (Averaging.smoothingRadius L) i j V b
def HasGluedCriticalOrbit (ε : ℝ) (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (W : Set (FourTorus L m)) (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    Prop :=
  HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k (gluedChain K n j Ω W)
    (gluedActiveSet K k n j Ω W) (gluedBoundaryData K k j Ω V)
def gluedCriticalConfiguration (ε : ℝ) (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (W : Set (FourTorus L m)) (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun U => U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
    (gluedChain K n j Ω W) (gluedActiveSet K k n j Ω W) (gluedBoundaryData K k j Ω V)
def partsMeet (K n : ℕ) (S : Finset ℕ) (A : ℕ → Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ standardCubePartition L m (scaledCubeIndex K 0 n) ∧ ∀ l ∈ S, Q ⊆ A l}
def partsDoubleInterior (K n : ℕ) (S : Finset ℕ) (A : ℕ → Set (FourTorus L m)) :
    Set (FourTorus L m) :=
  partsMeet K n S fun l => doubleInterior K n l (A l)
def partsCollar (K n : ℕ) (S : Finset ℕ) (A : ℕ → Set (FourTorus L m)) : Set (FourTorus L m) :=
  regionDiff (levelDepth K 0) (partsMeet K n S A) (partsDoubleInterior K n S A)
def IsCollarComponentInShell (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) (C : Set (FourTorus L m)) (l : ℕ) : Prop :=
  C ∈ regionComponents (levelDepth K 0) (partsCollar K n S A) ∧
    C ⊆ regionDiff (levelDepth K 0) (Ω l) (nextMember k Ω l)
def IsMultiShellGluableRegion (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) : Prop :=
  IsActiveSetSetting K k Ω ∧ S.Nonempty ∧ partsMeet K n S A ⊆ Ω 0 ∧
    (∀ l ∈ S, l ≤ k ∧ IsScaledCubeUnion K l n (A l) ∧
      cubeMeet K (partsMeet K n S A) (nextMember k Ω l) ⊆ doubleInterior K n l (A l) ∧
      partsMeet K n S A ⊆ Ω l ∪ doubleInterior K n l (A l)) ∧
    ∀ C ∈ regionComponents (levelDepth K 0) (partsCollar K n S A),
      ∃ l ∈ S, IsCollarComponentInShell K k n Ω S A C l
def multiShellGluedChain (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) (i : ℕ) : Set (FourTorus L m) :=
  cubeMeet K (Ω i) (partsDoubleInterior K n S A) ∪
    ⋃₀ {Q | Q ∈ partitionCubesIn (scaledCubeIndex K i n)
        (shrinkingTower K n 0 (partsMeet K n S A) i) ∧
      ¬Q ⊆ partsDoubleInterior K n S A ∧
      ∃ C, ∃ l ∈ S, i ≤ l ∧ IsCollarComponentInShell K k n Ω S A C l ∧
        (C ∩ (Q \ partsDoubleInterior K n S A)).Nonempty}
def multiShellGluedActiveSet (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) : Set (Σ q : ℕ, BondAtLevel L m K q) :=
  activeBondSet K k (multiShellGluedChain K k n Ω S A)
end PeriodicLattice
end YangMills.Construction
