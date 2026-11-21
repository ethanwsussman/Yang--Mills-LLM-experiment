import YangMills.Construction.Lattice.LengthOfAnEdgeGraph
import YangMills.Construction.Lattice.SizesInEdgesOfTreesMeetingAFamily
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
def cubeEdgeUnion (X : Set S.Points) : Set S.Points :=
  ⋃₀ {e | ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ}
def spanningTreeEdgeCounts (X : Set S.Points) (G : Set (Set S.Points)) : Set ℕ :=
  {e | ∃ Γ, IsSpanningEdgeTree S.index X G Γ ∧ (S.graphEdges Γ).ncard = e}
def IsSegmentSumLength (Γ : Set S.Points) (r : ℝ) : Prop :=
  (1 ≤ S.edgeCount Γ ∧ ∃ l, S.EnumeratesEdges (S.graphEdges Γ) l ∧
    TorusMetric.pathLength (S.edgeSegments l) = r) ∨
  (S.edgeCount Γ = 0 ∧ ∃ x ∈ Γ, ∃ z, S.IsPointLift x z ∧
    TorusMetric.pathLength [LevelUnitPartition.degenerateSegment z] = r)
def domainLinearExtent (X : Set S.Points) : ℝ :=
  linearExtent (L := S.params.L) (m := S.params.m) (S.params.K : ℕ) S.sideExponent S.level X
def CubeEdgeUnionIsTree (X : Set S.Points) : Prop :=
  (∀ Δ ∈ S.cubes, ∀ Δ' ∈ S.cubes, CubesShareFace S.index Δ Δ' →
    ∃ v, S.IsCornerOf v Δ ∧ S.IsCornerOf v Δ') ∧
  S.IsEdgeTreeInRegion X (S.cubeEdgeUnion X) ∧
  S.graphVertices (S.cubeEdgeUnion X) = {v | ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ} ∧
  (∀ R : Set S.Points, IsPartitionRegion S.index R → R ⊆ X → R.Nonempty →
    GraphIntersects (S.cubeEdgeUnion X) R) ∧
  {Γ : Set S.Points | S.IsGlobalEdgeGraph Γ ∧ Γ.Nonempty}.Finite
def MinimaExistFor (X : Set S.Points) (G : Set (Set S.Points)) : Prop :=
  {Γ | IsSpanningEdgeTree S.index X G Γ}.Finite ∧
  {Γ | IsSpanningEdgeTree S.index X G Γ}.Nonempty ∧
  S.IsAdmissibleTargetFamily X G ∧
  IsLeast (S.spanningTreeEdgeCounts X G) (S.minTreeEdges X G) ∧
  IsLeast {n | ∃ Γ, IsSpanningEdgeTree S.index X G Γ ∧ graphLength S.side S.index Γ = n}
    (minTreeLength S.side S.index X G) ∧
  (S.side : ℝ)⁻¹ * (minTreeLength S.side S.index X G : ℝ) =
    (S.minTreeEdges X G : ℝ) ∧
  ∃ r : ℝ, IsLeast {t | ∃ Γ, IsSpanningEdgeTree S.index X G Γ ∧ S.IsSegmentSumLength Γ t} r ∧
    (S.side : ℝ)⁻¹ * r = (S.minTreeEdges X G : ℝ)
def SizesAreMinimalEdgeCounts (X : Set S.Points) : Prop :=
  (∃ n : ℕ, S.domainLinearExtent X = (n : ℝ) ∧
    IsLeast (S.spanningTreeEdgeCounts X (partitionCubesIn S.index X)) n) ∧
  ∀ Z : Set S.Points, IsPartitionRegion S.index Z → (cubesNotIn S.index X Z).Nonempty →
    S.RelativeEdgeSizeDefined Z X ∧
      IsLeast (S.spanningTreeEdgeCounts X (cubesNotIn S.index X Z)) (S.relativeEdgeSize Z X)
def LinearExtentZeroIff (X : Set S.Points) : Prop :=
  (S.domainLinearExtent X = 0 ↔ ∃ v, ∀ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ) ∧
  (X ∈ S.cubes → S.domainLinearExtent X = 0)
def IslandRegionsAreDomains (I : Set (Set S.Points)) : Prop :=
  (∀ Y ∈ islandRegions S.index I, S.IsLevelDomain Y ∧ ¬Y ⊆ ⋃₀ I) ∧
  ∀ (first : Set S.Points → Prop) (Y : Set S.Points), S.IsLevelDomain Y → first Y →
    (¬Y ⊆ ⋃₀ I ∨ ¬partitionCubesIn S.index Y ⊆ partitionCubesIn S.index (⋃₀ I)) → ¬Y ⊆ ⋃₀ I
def IslandLengthIsMinimalEdgeCount (I : Set (Set S.Points)) (X : Set S.Points) : Prop :=
  ¬X ⊆ ⋃₀ I →
    (cubesNotIn S.index X (⋃₀ I)).Nonempty ∧
    S.IslandEdgeLengthDefined I X ∧
    IsLeast (S.spanningTreeEdgeCounts X (islandTreeTargets S.index I X)) (S.islandEdgeLength I X) ∧
    (∃ Γ, S.IsMinimalEdgeTree I X Γ) ∧
    (S.relativeEdgeSize (⋃₀ I) X : ℝ) ≤ (S.islandEdgeLength I X : ℝ) ∧
    (S.islandEdgeLength I X : ℝ) ≤ S.domainLinearExtent X ∧
    ((∀ B ∈ I, ¬(X ∩ B).Nonempty) →
      (S.relativeEdgeSize (⋃₀ I) X : ℝ) = (S.islandEdgeLength I X : ℝ) ∧
        (S.islandEdgeLength I X : ℝ) = S.domainLinearExtent X)
end LevelUnitPartition
def MinimalTreeSizes : Prop :=
  ∀ (S : LevelUnitPartition) (X : Set S.Points), S.IsLevelDomain X →
    (partitionCubesIn S.index X).Nonempty →
    S.CubeEdgeUnionIsTree X ∧
    (∀ G : Set (Set S.Points), G.Finite →
      (∀ A ∈ G, IsPartitionRegion S.index A ∧ A ⊆ X ∧ A.Nonempty) → S.MinimaExistFor X G) ∧
    S.SizesAreMinimalEdgeCounts X ∧
    S.LinearExtentZeroIff X ∧
    ∀ I : Set (Set S.Points), IsIslandCollection S.index I →
      S.IslandRegionsAreDomains I ∧ S.IslandLengthIsMinimalEdgeCount I X
end PeriodicLattice
end YangMills.Construction
