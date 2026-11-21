import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.SeparatedSequenceData
import Mathlib
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BaseParameters
variable (D : BaseParameters)
def torusSideInUnits : ℝ := 2 * (D.L : ℝ) ^ (D.m + D.K) * D.levelMeshRatio 0
def IsLiftCoordinate (x : D.Torus) (c : ℝ) : Prop :=
  ∃ w : Fin 4 → ℝ, PeriodicLattice.IsLevelLift D.L D.m D.K D.t x w ∧ ∃ μ, w μ = c
def orderMesh (i : ℕ) : ℝ := (D.L : ℝ) ^ i * D.levelMeshRatio 0
def orderCentreSet (i : ℕ) : Set D.Torus :=
  {y | ∃ w : Fin 4 → ℝ, PeriodicLattice.IsLevelLift D.L D.m D.K D.t y w ∧
    ∀ μ, ∃ n : ℤ, w μ = D.orderMesh i * (n : ℝ)}
def supDist (x y : D.Torus) : ℝ := D.lengthInUnits (TorusMetric.torusSupNorm (x - y))
def closedOrderCube (i : ℕ) (y : D.orderCentreSet i) : Set D.Torus :=
  {x | D.supDist x y ≤ D.orderMesh i / 2}
def openOrderCube (i : ℕ) (y : D.orderCentreSet i) : Set D.Torus :=
  {x | D.supDist x y < D.orderMesh i / 2}
def IsOrderCubeCentre (i : ℕ) (y : D.Torus) (C : Set D.Torus) : Prop :=
  i ≤ D.m + D.K ∧ ∃ h : y ∈ D.orderCentreSet i, C = D.closedOrderCube i ⟨y, h⟩
def IsOrderCube (i : ℕ) (C : Set D.Torus) : Prop := ∃ y, D.IsOrderCubeCentre i y C
variable {D}
def openOrderCubeAt {n : ℕ} (y : D.orderCentreSet n) : Set D.Torus := D.openOrderCube n y
end YangMills.Construction.SeparatedSequences.BaseParameters
end
