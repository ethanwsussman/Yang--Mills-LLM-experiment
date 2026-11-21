import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Torus
variable {d : ℕ} {S : ℝ}
def openEuclidCube (c : Fin d → ℝ) (s : ℝ) : Set (Fin d → ℝ) := {v | ∀ μ, |v μ - c μ| < s / 2}
def IsSegmentPath (S : ℝ) : PeriodicTorus d S → PeriodicTorus d S → List (TorusSegment d) → Prop
  | p, q, [] => p = q
  | p, q, s :: Γ => s.pointAt S 0 = p ∧ IsSegmentPath S (s.pointAt S 1) q Γ
def segmentPathLength (Γ : List (TorusSegment d)) : ℝ := (Γ.map TorusSegment.lOneLength).sum
def centredIntVectors (d : ℕ) (N : ℝ) : Set (Fin d → ℤ) := {k | ∀ μ, |(k μ : ℝ)| ≤ (N - 1) / 2}
def gridImage (S σ : ℝ) (z : Fin d → ℝ) (k : Fin d → ℤ) : PeriodicTorus d S :=
  torusProj d S fun μ => z μ + σ * (k μ : ℝ)
structure IsCenteredGrid (S σ N : ℝ) (z : Fin d → ℝ) (P : Set (PeriodicTorus d S)) : Prop where
  image_eq : gridImage S σ z '' centredIntVectors d N = P
  injOn : InjOn (gridImage S σ z) (centredIntVectors d N)
  ncard_eq : ((centredIntVectors d N).ncard : ℝ) = N ^ d
def IsNatAtLeastTwo (r : ℝ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ r = k
def IsPosEvenNat (r : ℝ) : Prop := ∃ k : ℕ, 0 < k ∧ r = 2 * (k : ℝ)
def IsAdmissibleSide (L : ℕ) (ξ S τ : ℝ) : Prop :=
  ∃ i : ℤ, τ = scaleSpacing L ξ i ∧ IsNatAtLeastTwo (S / τ)
structure ProjectionFacts (d : ℕ) (S : ℝ) : Prop where
  injOn : ∀ (c : Fin d → ℝ) (s : ℝ), s ≤ S → InjOn (torusProj d S) (openEuclidCube c s)
  supNorm_eq : ∀ v w : Fin d → ℝ, ‖v - w‖ ≤ S / 2 →
    supNorm (torusProj d S v - torusProj d S w) = ‖v - w‖
  lOneNorm_eq : ∀ v w : Fin d → ℝ, ‖v - w‖ ≤ S / 2 →
    lOneNorm (torusProj d S v - torusProj d S w) = ∑ μ, |v μ - w μ|
  lOneNorm_le_length : ∀ (p q : PeriodicTorus d S) (Γ : List (TorusSegment d)),
    IsSegmentPath S p q Γ → lOneNorm (p - q) ≤ segmentPathLength Γ
structure NestedPartitionFacts (d L : ℕ) (ξ S σ σ' : ℝ) : Prop where
  div_eq_int : ∃ k : ℤ, S / σ' = k
  spacingLattice_le : spacingLattice d S σ ≤ spacingLattice d S σ'
  not_mem_of_mem_interior : ∀ Q ∈ cubePartition d S σ, ∀ Q' ∈ cubePartition d S σ,
    Q' ≠ Q → ∀ p ∈ interior Q, p ∉ Q'
  eq_sUnion_finer : ∀ Q ∈ cubePartition d S σ,
    Q = ⋃₀ {Q' ∈ cubePartition d S σ' | Q' ⊆ Q}
  isCubeUnion_finer : ∀ X : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ' X
  grid_in_cube : ∀ z ∈ spacingLattice d S σ, ∀ z' : Fin d → ℝ, torusProj d S z' = z →
    IsCenteredGrid S σ' (σ / σ') z' ((spacingLattice d S σ' : Set (PeriodicTorus d S)) ∩ cubeAt z σ)
  grid_subset_interior : ∀ z ∈ spacingLattice d S σ,
    (spacingLattice d S σ' : Set (PeriodicTorus d S)) ∩ cubeAt z σ ⊆ interior (cubeAt z σ)
  closure_sdiff : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y → Y ⊆ X →
    closure (X \ Y) = ⋃₀ {Q ∈ cubePartition d S σ | Q ⊆ X ∧ ¬ Q ⊆ Y}
  disjoint_interior : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y →
    Y ⊆ X → ∀ Q ∈ cubePartition d S σ, Q ⊆ X → ¬ Q ⊆ Y → Disjoint (interior Q) Y
  compl_subset : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y → Yᶜ ⊆ cubeComplement σ Y
  frontier_subset : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
    frontier Y ⊆ cubeComplement σ Y
  cubeComplement_anti : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y →
    Y ⊆ X → cubeComplement σ X ⊆ cubeComplement σ Y
  cubeComplement_eq_closure : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
    ∀ τ, IsAdmissibleSide L ξ S τ → IsCubeUnion τ Y → cubeComplement τ Y = closure Yᶜ
def ScaleSideFacts (d L : ℕ) (ξ S σ : ℝ) : Prop :=
  ∃ i : ℤ, σ = scaleSpacing L ξ i ∧ IsPosEvenNat (S / σ) ∧
    ∀ i' : ℤ, i' ≤ i → NestedPartitionFacts d L ξ S σ (scaleSpacing L ξ i')
structure ChainSideFacts (d L : ℕ) (ξ S : ℝ) (M : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) :
    Prop where
  block_side : ∀ n ≤ lastNonemptyIndex Ω, ScaleSideFacts d L ξ S ((M : ℝ) * scaleSpacing L ξ n)
  spacing_side : ∀ n ≤ lastNonemptyIndex Ω, ScaleSideFacts d L ξ S (scaleSpacing L ξ n)
  next_spacing_side : ScaleSideFacts d L ξ S (scaleSpacing L ξ ((lastNonemptyIndex Ω : ℤ) + 1))
  two_block_le : ∀ n, (Ω n).Nonempty → 2 * (M : ℝ) * scaleSpacing L ξ n ≤ S
structure ChainMemberFacts (L : ℕ) (ξ : ℝ) (M t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) :
    Prop where
  isCubeUnion : ∀ n ≤ lastNonemptyIndex Ω, IsCubeUnion ((M : ℝ) * scaleSpacing L ξ n) (Ω n)
  isCubeUnion_succ : ∀ n ≤ lastNonemptyIndex Ω,
    IsCubeUnion ((M : ℝ) * scaleSpacing L ξ n) (Ω (n + 1))
  shell_eq : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n =
    ⋃₀ {Q ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n) | Q ⊆ Ω n ∧ ¬ Q ⊆ Ω (n + 1)}
  shell_subset : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n ⊆
    Ω n ∩ cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω (n + 1))
  zero_eq_iUnion : Ω 0 = ⋃ m ∈ Iic (lastNonemptyIndex Ω), shell Ω m
  shell_eq_empty : ∀ m, lastNonemptyIndex Ω < m → m ≤ t → shell Ω m = ∅
structure ShellCubeFacts (L : ℕ) (ξ : ℝ) (M t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) (n : ℕ) :
    Prop where
  siteCubes_eq : {Q | ∃ y ∈ shellSites L ξ Ω n, Q = siteCube L ξ Ω y} =
    {Q ∈ cubePartition d S (scaleSpacing L ξ n) | Q ⊆ shell Ω n}
  shell_eq_iUnion : shell Ω n = ⋃ y ∈ shellSites L ξ Ω n, siteCube L ξ Ω y
  disjoint_cubeComplement : ∀ y ∈ shellSites L ξ Ω n, Disjoint (interior (siteCube L ξ Ω y))
    (cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω n))
  disjoint_succ : ∀ y ∈ shellSites L ξ Ω n,
    Disjoint (interior (siteCube L ξ Ω y)) (Ω (n + 1))
  disjoint_shell : ∀ y ∈ shellSites L ξ Ω n, ∀ m ≤ t, m ≠ n →
    Disjoint (interior (siteCube L ξ Ω y)) (shell Ω m)
  disjoint_siteCube : ∀ y ∈ shellSites L ξ Ω n, ∀ y' ∈ unionShellSites L ξ t Ω, y' ≠ y →
    Disjoint (interior (siteCube L ξ Ω y)) (siteCube L ξ Ω y')
  mem_interior_shell : ∀ y ∈ shellSites L ξ Ω n, y ∈ interior (shell Ω n)
structure SiteLocationFacts (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  exists_of_mem : ∀ x ∈ spacingLattice d S ξ, x ∈ Ω 0 → ∃ y ∈ unionShellSites L ξ t Ω,
    x ∈ interior (siteCube L ξ Ω y) ∧
    (∀ y' ∈ unionShellSites L ξ t Ω, y' ≠ y → x ∉ siteCube L ξ Ω y') ∧
    cubeAt x ξ ⊆ siteCube L ξ Ω y ∧
    ∀ m, y ∈ shellSites L ξ Ω m → x ∈ shell Ω m ∧ ∀ m' ≤ t, m' ≠ m → x ∉ shell Ω m'
  disjoint_of_not_mem : ∀ x ∈ spacingLattice d S ξ, x ∉ Ω 0 →
    Disjoint (interior (cubeAt x ξ)) (Ω 0)
def BoxGridAdj {N : ℕ} (a b : Fin d → Fin N) : Prop :=
  ∃ μ, (SimpleGraph.pathGraph N).Adj (a μ) (b μ) ∧ ∀ ν, ν ≠ μ → a ν = b ν
structure CubeSiteFacts (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S)
    (z : Fin d → ℝ) : Prop where
  isCenteredGrid : IsCenteredGrid S ξ (shellSpacing L ξ Ω y / ξ) z
    ((spacingLattice d S ξ : Set (PeriodicTorus d S)) ∩ siteCube L ξ Ω y)
  isNeighbor_iff : ∀ k ∈ centredIntVectors d (shellSpacing L ξ Ω y / ξ),
    ∀ k' ∈ centredIntVectors d (shellSpacing L ξ Ω y / ξ),
    ∀ x x' : LatticeSite d S ξ,
      (x : PeriodicTorus d S) = gridImage S ξ z k → (x' : PeriodicTorus d S) = gridImage S ξ z k' →
      (IsNeighbor x x' ↔ ∃ μ, k' = k + Pi.single μ 1 ∨ k' = k - Pi.single μ 1)
  equiv_boxGrid : ∃ N : ℕ, (N : ℝ) = shellSpacing L ξ Ω y / ξ ∧
    ∃ e : (Fin d → Fin N) ≃ {x : LatticeSite d S ξ // (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y},
      ∀ a b, IsNeighbor (e a).1 (e b).1 ↔ BoxGridAdj a b
  exists_geodesic : ∀ x x' : LatticeSite d S ξ,
    (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y → (x' : PeriodicTorus d S) ∈ siteCube L ξ Ω y →
    ∃ (r : ℕ) (w : ℕ → LatticeSite d S ξ),
      (r : ℝ) = lOneNorm ((x : PeriodicTorus d S) - (x' : PeriodicTorus d S)) / ξ ∧ w 0 = x ∧
      w r = x' ∧ (∀ i < r, IsNeighbor (w i) (w (i + 1))) ∧
      ∀ i ≤ r, (w i : PeriodicTorus d S) ∈ siteCube L ξ Ω y
  lOneNorm_sub_centre_le : ∀ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y →
    lOneNorm ((x : PeriodicTorus d S) - y) ≤ 1 / 2 * (d : ℝ) * shellSpacing L ξ Ω y
def PartitionsHold : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus → ∀ ξ S : ℝ, 0 < ξ → 0 < S →
    ProjectionFacts d S ∧
    (∀ i' i : ℤ, i' ≤ i → IsNatAtLeastTwo (S / scaleSpacing L ξ i) →
      NestedPartitionFacts d L ξ S (scaleSpacing L ξ i) (scaleSpacing L ξ i')) ∧
    ∀ (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), IsSeparatedChain L ξ M R₁ t Ω →
      ChainSideFacts d L ξ S M Ω ∧ ChainMemberFacts L ξ M t Ω ∧
      (∀ n ≤ lastNonemptyIndex Ω, ShellCubeFacts L ξ M t Ω n) ∧ SiteLocationFacts L ξ t Ω ∧
      (∀ n ≤ lastNonemptyIndex Ω, ∀ y ∈ shellSites L ξ Ω n, ∀ z : Fin d → ℝ, torusProj d S z = y →
        CubeSiteFacts L ξ Ω y z) ∧
      ∀ x : LatticeSite d S ξ, {x' | IsNeighbor x x'}.ncard = 2 * d
end YangMills.Construction.Torus
end
