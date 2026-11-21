import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def connectedRegions (L m : ℕ) (i : ℤ) : Set (Set (FourTorus L m)) :=
  {X | IsPartitionRegion i X ∧ IsFaceConnectedRegion i X}
def HaveCommonFace (i : ℤ) (Q Q' : Set (FourTorus L m)) : Prop :=
  ∃ F, IsCubeFace i F Q ∧ IsCubeFace i F Q'
def faceChainConnectedRegions (L m : ℕ) (i : ℤ) : Set (Set (FourTorus L m)) :=
  {X | IsPartitionRegion i X ∧ ∀ Q ∈ partitionCubesIn i X, ∀ Q' ∈ partitionCubesIn i X,
    ∃ c : List (Set (FourTorus L m)), (∀ P ∈ c, P ∈ partitionCubesIn i X) ∧
      c.IsChain (HaveCommonFace i) ∧ c.head? = some Q ∧ c.getLast? = some Q'}
def IsCubeVertex (i : ℤ) (c : FourTorus L m) (Q : Set (FourTorus L m)) : Prop :=
  ∃ y : Site L m i, Q = cubeAround y ∧ ∃ s : Fin 4 → ℝ, (∀ ν, s ν = 1 ∨ s ν = -1) ∧
    ∀ ν, c ν = (y : FourTorus L m) ν + ((s ν * meshSize L i / 2 : ℝ) : AddCircle (torusSide L m))
def IsCubeEdge (i : ℤ) (e Q : Set (FourTorus L m)) : Prop :=
  ∃ y : Site L m i, Q = cubeAround y ∧ ∃ (μ : Fin 4) (s : Fin 4 → ℝ), (∀ ν, s ν = 1 ∨ s ν = -1) ∧
    e = {x | x ∈ Q ∧ ∀ ν, ν ≠ μ →
      x ν = (y : FourTorus L m) ν + ((s ν * meshSize L i / 2 : ℝ) : AddCircle (torusSide L m))}
def IsEdgeGraph (i : ℤ) (X Γ : Set (FourTorus L m)) : Prop :=
  (∃ Q ∈ partitionCubesIn i X, ∃ c, IsCubeVertex i c Q ∧ Γ = {c}) ∨
    ∃ E : Set (Set (FourTorus L m)), (∀ e ∈ E, ∃ Q ∈ partitionCubesIn i X, IsCubeEdge i e Q) ∧
      Γ = ⋃₀ E
def IsEdgeTree (i : ℤ) (X Γ : Set (FourTorus L m)) : Prop :=
  IsEdgeGraph i X Γ ∧ IsConnected Γ
def edgeCount (i : ℤ) (Γ : Set (FourTorus L m)) : ℕ :=
  {e | (∃ Q ∈ standardCubePartition L m i, IsCubeEdge i e Q) ∧ e ⊆ Γ}.ncard
def graphLength (M : ℕ) (i : ℤ) (Γ : Set (FourTorus L m)) : ℕ := M * edgeCount i Γ
theorem graphLength_le_graphLength_iff {M : ℕ} (hM : 0 < M) (i : ℤ) (Γ Γ' : Set (FourTorus L m)) :
    graphLength M i Γ ≤ graphLength M i Γ' ↔ edgeCount i Γ ≤ edgeCount i Γ' :=
  Nat.mul_le_mul_left_iff hM
def GraphIntersects (Γ A : Set (FourTorus L m)) : Prop := (Γ ∩ A).Nonempty
def IsSpanningEdgeTree (i : ℤ) (X : Set (FourTorus L m)) (G : Set (Set (FourTorus L m)))
    (Γ : Set (FourTorus L m)) : Prop :=
  IsEdgeTree i X Γ ∧ ∀ A ∈ G, GraphIntersects Γ A
def minTreeLength (M : ℕ) (i : ℤ) (X : Set (FourTorus L m)) (G : Set (Set (FourTorus L m))) : ℕ :=
  sInf {n | ∃ Γ, IsSpanningEdgeTree i X G Γ ∧ graphLength M i Γ = n}
def linearExtent (K m' j : ℕ) (X : Set (FourTorus L m)) : ℝ :=
  ((L ^ m' : ℕ) : ℝ)⁻¹ *
    minTreeLength (L ^ m') (coarseCubeIndex K m' j) X (partitionCubesIn (coarseCubeIndex K m' j) X)
def cubesNotIn (i : ℤ) (X Z : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  partitionCubesIn i X \ partitionCubesIn i Z
open Classical in
def relativeLinearExtent (K m' j : ℕ) (Z X : Set (FourTorus L m)) : ℝ :=
  if ∀ Q ∈ partitionCubesIn (coarseCubeIndex K m' j) X, Q ⊆ Z then 0
  else ((L ^ m' : ℕ) : ℝ)⁻¹ *
    minTreeLength (L ^ m') (coarseCubeIndex K m' j) X (cubesNotIn (coarseCubeIndex K m' j) X Z)
def IsIslandCollection (i : ℤ) (I : Set (Set (FourTorus L m))) : Prop :=
  I.Finite ∧ (∀ B ∈ I, IsPartitionBox i B) ∧ I.Pairwise fun B B' => ¬RegionsMeet i B B'
def islandRegions (i : ℤ) (I : Set (Set (FourTorus L m))) : Set (Set (FourTorus L m)) :=
  {X | X ∈ connectedRegions L m i ∧ (∃ J ⊆ I, X ∩ ⋃₀ I = ⋃₀ J) ∧ ¬X ⊆ ⋃₀ I}
def islandTreeTargets (i : ℤ) (I : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) :
    Set (Set (FourTorus L m)) :=
  cubesNotIn i X (⋃₀ I) ∪ {B | B ∈ I ∧ B ⊆ X}
def islandLinearExtent (K m' j : ℕ) (I : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) : ℝ :=
  ((L ^ m' : ℕ) : ℝ)⁻¹ *
    minTreeLength (L ^ m') (coarseCubeIndex K m' j) X (islandTreeTargets (coarseCubeIndex K m' j) I X)
end YangMills.Construction.PeriodicLattice
