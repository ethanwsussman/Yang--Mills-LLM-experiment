import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import YangMills.Construction.Lattice.MinimaThatSetTheSizes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TorusBound
open YangMills.Construction.PeriodicLattice
namespace Setup
variable (D : Setup)
abbrev levelCubeSide (j : ℕ) : ℝ := (D.cubeSide : ℝ) * meshSize D.L (D.depthOf j)
def IsCubeOfSide (j : ℕ) (t : ℝ) (Q : Set D.Torus) : Prop :=
  ∃ y : Site D.L D.m (D.cubeScaleIndex j),
    Q = {x | TorusMetric.torusSupNorm (x - (y : D.Torus)) ≤ t / 2}
def MeshLeLevelCubeSide (j : ℕ) : Prop :=
  D.levelCubeSide j = (D.cubeSide : ℝ) * (D.L : ℝ) ^ (-D.depthOf j) ∧
    meshSize D.L (D.K : ℤ) ≤ D.levelCubeSide j
def CountsAtFittingLevel (j : ℕ) : Prop :=
  (∃ n : ℤ, Even n ∧ D.side / D.levelCubeSide j = (n : ℝ)) ∧
  (∀ Q ∈ D.cubesAt j, D.IsCubeOfSide j (D.levelCubeSide j) Q) ∧
  (D.cubesAt j).Finite ∧
  ((D.cubesAt j).ncard : ℝ) = (D.side / D.levelCubeSide j) ^ 4 ∧
  ∀ d : DomainKind, (D.regionsBy d j).Finite
def spanningTreeEdgeCounts {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j)
    (X : Set D.Torus) : Set ℕ :=
  {E | ∃ Γ : Set D.Torus, IsEdgeTreeWithCount (D.levelUnitPartition hj h) X Γ E ∧
    ∀ Q ∈ partitionCubesIn (D.cubeScaleIndex j) X, GraphIntersects Γ Q}
def AllEdgesTreeAndSize {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j)
    (X : Set D.Torus) : Prop :=
  _root_.IsConnected ((D.levelUnitPartition hj h).cubeEdgeUnion X) ∧
  (D.levelUnitPartition hj h).IsEdgeTreeInRegion X ((D.levelUnitPartition hj h).cubeEdgeUnion X) ∧
  (∀ Q ∈ partitionCubesIn (D.cubeScaleIndex j) X,
    GraphIntersects ((D.levelUnitPartition hj h).cubeEdgeUnion X) Q) ∧
  (D.spanningTreeEdgeCounts hj h X).Nonempty ∧
  ∃ n : ℕ, D.extent j X = (n : ℝ) ∧ IsLeast (D.spanningTreeEdgeCounts hj h X) n
end Setup
def CubeSidesAndLinearSize : Prop :=
  ∀ (D : Setup) (j : ℕ) (hj : j ≤ D.K),
    D.MeshLeLevelCubeSide j ∧
    ∀ h : D.LevelFits j,
      D.CountsAtFittingLevel j ∧
      ∀ (d : DomainKind) (X : Set D.Torus), X ∈ D.regionsBy d j →
        ((partitionCubesIn (D.cubeScaleIndex j) X).Nonempty → D.AllEdgesTreeAndSize hj h X) ∧
        ((D.plaquettesOfThickened j X).Nonempty → (partitionCubesIn (D.cubeScaleIndex j) X).Nonempty)
end TorusBound
end YangMills.Construction
end
