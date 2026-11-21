import YangMills.Construction.Lattice.CubesVerticesAndEdgesInPhysicalUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice TorusMetric
namespace TorusBound
namespace PartitionCells
variable (D : Setup) {j : ℕ}
def VertexCubeIncidence (hj : j ≤ D.K) (h : D.LevelFits j) : Prop :=
  (∀ (c : Site D.L D.m (D.cubeScaleIndex j)) (v : D.Torus), D.IsLevelVertex hj h v →
    (v ∈ D.cubeCentredAt c ↔
      ∃ wc wv : Fin 4 → ℝ, D.IsLiftOfPoint (c : D.Torus) wc ∧ D.IsLiftOfPoint v wv ∧
        ∀ μ, wc μ - wv μ = D.physicalCubeSide j / 2 ∨ wc μ - wv μ = -(D.physicalCubeSide j / 2)) ∧
    (v ∈ D.cubeCentredAt c ↔ (D.levelUnitPartition hj h).IsCornerOf v (D.cubeCentredAt c))) ∧
  (∀ Q : Set D.Torus, D.IsLevelCube j Q →
    {v : D.Torus | (D.levelUnitPartition hj h).IsCornerOf v Q}.encard = 16) ∧
  ∀ v : D.Torus, D.IsLevelVertex hj h v → {Q : Set D.Torus | D.IsLevelCube j Q ∧ v ∈ Q}.encard ≤ 16
def EdgesMeetAtEndpoints (hj : j ≤ D.K) (h : D.LevelFits j) : Prop :=
  ∀ A A' : Set D.Torus, D.IsLevelEdge hj h A → D.IsLevelEdge hj h A' → A ≠ A' → ∀ y ∈ A ∩ A',
    (D.levelUnitPartition hj h).IsEdgeEndpoint A y ∧ (D.levelUnitPartition hj h).IsEdgeEndpoint A' y
def CubeMeetingEdgeContainsEndpoint (hj : j ≤ D.K) (h : D.LevelFits j) : Prop :=
  ∀ Q A : Set D.Torus, D.IsLevelCube j Q → D.IsLevelEdge hj h A → CubeIntersects Q A →
    ∃ y ∈ Q, (D.levelUnitPartition hj h).IsEdgeEndpoint A y
def CubeDistanceBounds (hj : j ≤ D.K) (h : D.LevelFits j) : Prop :=
  (∀ Q : Set D.Torus, D.IsLevelCube j Q → ∀ x ∈ Q, ∀ y ∈ Q,
    torusSupNorm (x - y) ≤ D.physicalCubeSide j) ∧
  (∀ (c : Site D.L D.m (D.cubeScaleIndex j)) (Q : Set D.Torus), D.IsLevelCube j Q →
    CubesMeet Q (D.cubeCentredAt c) → ∀ q ∈ Q,
      torusSupNorm (q - (c : D.Torus)) ≤ 3 / 2 * D.physicalCubeSide j ∧
      ∀ y ∈ D.cubeCentredAt c,
        torusSupNorm (q - y) ≤ 2 * D.physicalCubeSide j ∧
        torusEuclidNorm (q - y) ≤ 4 * D.physicalCubeSide j) ∧
  ∀ A : Set D.Torus, D.IsLevelEdge hj h A → ∀ u u' : D.Torus,
    (D.levelUnitPartition hj h).IsEdgeEndpoint A u → (D.levelUnitPartition hj h).IsEdgeEndpoint A u' →
      torusEuclidNorm (u - u') ≤ D.physicalCubeSide j
def cubesWithinSupDist (j : ℕ) (y₀ : D.Torus) (ρ' : ℝ) : Set (Set D.Torus) :=
  {Q | ∃ c : Site D.L D.m (D.cubeScaleIndex j), Q = D.cubeCentredAt c ∧
    torusSupNorm ((c : D.Torus) - y₀) ≤ ρ'}
def CubeCountNearPoint (j : ℕ) : Prop :=
  ∀ (y₀ : D.Torus) (ρ' : ℝ), 0 ≤ ρ' →
    (cubesWithinSupDist D j y₀ ρ').Finite ∧
      ((cubesWithinSupDist D j y₀ ρ').ncard : ℝ) ≤ (2 * ρ' / D.physicalCubeSide j + 1) ^ 4
def Holds : Prop :=
  ∀ (D : Setup) (j : ℕ) (hj : j ≤ D.K) (h : D.LevelFits j),
    VertexCubeIncidence D hj h ∧ EdgesMeetAtEndpoints D hj h ∧
      CubeMeetingEdgeContainsEndpoint D hj h ∧ CubeDistanceBounds D hj h ∧
      CubeCountNearPoint D j
end PartitionCells
end TorusBound
end YangMills.Construction
end
