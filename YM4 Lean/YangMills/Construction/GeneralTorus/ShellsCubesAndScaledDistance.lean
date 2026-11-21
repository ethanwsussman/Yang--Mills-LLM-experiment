import YangMills.Construction.Geometry.ToriGeneralSide
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace ScaleData
variable (D : ScaleData)
def centeredBox (N : ℕ) : Set (Fin 4 → ℤ) := {k | ∀ ν, |(k ν : ℝ)| ≤ ((N : ℝ) - 1) / 2}
def translateBy (s : ℝ) (y : D.Space) (k : Fin 4 → ℤ) : D.Space :=
  y + torusProj D.torusSide fun ν => s * (k ν : ℝ)
def sitesInCubeAt (m n : ℕ) (y : D.Space) : Set D.Space :=
  (D.levelSublattice m : Set D.Space) ∩ D.cubeAt n y
def CubeSubdivision : Prop :=
  ∀ m n : ℕ, m ≤ n → D.AdmitsPartition (D.levelSpacing n) → ∀ y ∈ D.levelSublattice n,
    D.sitesInCubeAt m n y = D.translateBy (D.levelSpacing m) y '' centeredBox (D.L ^ (n - m)) ∧
    InjOn (D.translateBy (D.levelSpacing m) y) (centeredBox (D.L ^ (n - m))) ∧
    (D.sitesInCubeAt m n y).ncard = D.L ^ ((n - m) * 4) ∧
    D.sitesInCubeAt m n y ⊆ interior (D.cubeAt n y) ∧
    D.cubeAt n y = ⋃ z ∈ D.sitesInCubeAt m n y, D.cubeAt m z
def BaseBlockEqSites : Prop :=
  ∀ n : ℕ, D.AdmitsPartition (D.levelSpacing n) → ∀ y ∈ D.levelSublattice n,
    D.baseBlock n y = D.translateBy D.baseSpacing y '' centeredBox (D.L ^ n) ∧
    D.baseBlock n y = D.sitesInCubeAt 0 n y ∧
    (D.baseBlock n y).ncard = (D.L ^ n) ^ 4
def CoarseBlockEqSites : Prop :=
  ∀ k : ℕ, D.AdmitsPartition (D.levelSpacing (k + 1)) → ∀ y ∈ D.levelSublattice (k + 1),
    D.coarseBlock k y = D.sitesInCubeAt k (k + 1) y ∧
    (D.coarseBlock k y).ncard = D.L ^ 4 ∧
    D.baseBlock (k + 1) y = ⋃ z ∈ D.coarseBlock k y, D.baseBlock k z ∧
    (D.coarseBlock k y).PairwiseDisjoint (D.baseBlock k)
def SitesNotOnCubeFrontier : Prop :=
  ∀ m : ℕ, D.AdmitsPartition (D.levelSpacing m) → ∀ π : Set (Set D.Space), D.IsStdPartition π →
    ∀ Q ∈ π, ∀ z ∈ D.levelSublattice m, z ∉ frontier Q
end ScaleData
namespace SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def SetsAreCubeUnions : Prop :=
  ∀ m n : ℕ, m ≤ n → n ≤ D.lastLevel →
    ((B.set n).Nonempty → D.AdmitsPartition (D.blockLength n) ∧ D.AdmitsPartition (D.blockLength m)) ∧
    IsUnionOfCubes (D.cubePartition (D.levelSpacing m)) (B.set n) ∧
    IsUnionOfCubes (D.cubePartition (D.levelSpacing m)) (B.set (n + 1)) ∧
    ((B.set n).Nonempty →
      IsUnionOfCubes (D.blockPartition m) (B.set n) ∧
        IsUnionOfCubes (D.blockPartition m) (B.set (n + 1))) ∧
    ∀ z ∈ D.levelSublattice m, ∀ X ∈ ({B.set n, B.set (n + 1)} : Set (Set D.Space)),
      (z ∈ X → D.cubeAt m z ⊆ X) ∧ (z ∉ X → Disjoint (interior (D.cubeAt m z)) X)
def ShellsAreCubeUnions : Prop :=
  ∀ n : ℕ, n ≤ D.lastLevel →
    B.shell n =
      ⋃₀ {Q ∈ D.cubePartition (D.levelSpacing n) | Q ⊆ B.set n ∧ ¬Q ⊆ B.set (n + 1)} ∧
    B.shell n ⊆ closedComplement (B.set (n + 1)) ∧
    B.shellSites n =
      {y ∈ (D.levelSublattice n : Set D.Space) | y ∈ B.set n ∧ y ∉ B.set (n + 1)} ∧
    B.shell n = ⋃ y ∈ B.shellSites n, B.localCube y ∧
    (∀ U : Set D.Space, IsOpen U → U ⊆ B.set n → Disjoint U (B.set (n + 1)) →
      ∀ m : ℕ, m ≤ D.lastLevel → m ≠ n → Disjoint U (B.shell m)) ∧
    ∀ y ∈ B.shellSites n,
      interior (B.localCube y) ⊆ B.set n ∧ Disjoint (interior (B.localCube y)) (B.set (n + 1))
def LocalCubesInteriorsDisjoint : Prop :=
  ∀ y ∈ B.shellSitesUnion, ∀ y' ∈ B.shellSitesUnion, y ≠ y' →
    Disjoint (interior (B.localCube y)) (interior (B.localCube y'))
def BaseSitesInUniqueLocalCube : Prop :=
  ∀ x ∈ D.baseLattice, x ∈ B.set 0 →
    (∃! y, y ∈ B.shellSitesUnion ∧ x ∈ B.localCube y) ∧
    ∀ y ∈ B.shellSitesUnion, x ∈ B.localCube y → ∀ n : ℕ, IsGreatest {i | x ∈ B.set i} n →
      B.localCube y ∈ D.cubePartition (D.levelSpacing n) ∧ x ∈ interior (B.localCube y) ∧
        D.cubeAt 0 x ⊆ B.localCube y
def ScaledDistIsPseudometric : Prop :=
  (∀ x x' : D.Space, ∃ Γ : List LiftedSegment,
    IsTreeGraph D.torusSide Γ ∧ x ∈ segmentsSupport D.torusSide Γ ∧ x' ∈ segmentsSupport D.torusSide Γ) ∧
  (∀ Γ : List LiftedSegment, 0 ≤ B.scaledLength Γ) ∧
  (∀ x x' : D.Space, B.scaledDist x x' = B.scaledDist x' x) ∧
  (∀ x : D.Space, B.scaledDist x x = 0) ∧
  ∀ x x' x'' : D.Space,
    B.scaledDist x x'' ≤ B.scaledDist x x' + B.scaledDist x' x''
end SeparatedChain
def SeparatedChainStructure : Prop :=
  ∀ (D : ScaleData) (B : SeparatedChain D),
    B.SetsAreCubeUnions ∧
    B.ShellsAreCubeUnions ∧
    B.LocalCubesInteriorsDisjoint ∧
    D.CubeSubdivision ∧
    D.BaseBlockEqSites ∧
    D.CoarseBlockEqSites ∧
    D.SitesNotOnCubeFrontier ∧
    B.BaseSitesInUniqueLocalCube ∧
    B.ScaledDistIsPseudometric
end YangMills.Construction.GeneralTorus
end
