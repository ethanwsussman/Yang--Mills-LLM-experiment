import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeLifts
variable (S : LevelUnitPartition)
def scaledTorusSide : ℝ := S.params.side * (S.params.L : ℝ) ^ levelDepth S.params.K S.level
def IsCubeCentre (c : Fin 4 → ℝ) : Prop :=
  ∀ μ, ∃ a : ℤ, c μ = (S.side : ℝ) * (a : ℝ)
def IsPeriodVector (r : Fin 4 → ℝ) : Prop :=
  ∃ a : Fin 4 → ℤ, ∀ μ, r μ = (S.cubeCount : ℝ) * (S.side : ℝ) * (a μ : ℝ)
def TorusInCubeUnits : Prop :=
  -((S.params.m : ℕ) : ℤ) ≤ S.index ∧
  (S.side : ℝ) * meshSize S.params.L (levelDepth S.params.K S.level) =
    meshSize S.params.L S.index ∧
  S.cubes = standardCubePartition S.params.L S.params.m S.index ∧
  toLevelUnits S.params.L S.params.K S.level (meshSize S.params.L S.index) =
    (S.side : ℝ) ∧
  toLevelUnits S.params.L S.params.K S.level S.params.side = scaledTorusSide S ∧
  scaledTorusSide S = (S.cubeCount : ℝ) * (S.side : ℝ) ∧
  (∀ x : S.Points, ∃ w, S.IsPointLift x w) ∧
  (∀ w w' : Fin 4 → ℝ,
    (∃ x : S.Points, S.IsPointLift x w ∧ S.IsPointLift x w') ↔ IsPeriodVector S (w - w')) ∧
  Even S.cubeCount ∧ 2 ≤ S.cubeCount ∧ 0 < S.side
def CubeCountDichotomy : Prop :=
  (3 ≤ S.cubeCount ↔ 3 * (S.side : ℝ) ≤ scaledTorusSide S) ∧
  (3 ≤ S.cubeCount ↔
    (S.sideExponent : ℤ) < ((S.params.m : ℕ) : ℤ) + ((S.params.K : ℕ) : ℤ) - S.level) ∧
  (3 ≤ S.cubeCount → 2 * S.params.L ≤ S.cubeCount) ∧
  Xor (S.cubeCount = 2) (3 ≤ S.cubeCount) ∧
  (S.cubeCount = 2 ↔ scaledTorusSide S = 2 * (S.side : ℝ)) ∧
  (S.cubeCount = 2 ↔
    (S.sideExponent : ℤ) = ((S.params.m : ℕ) : ℤ) + ((S.params.K : ℕ) : ℤ) - S.level) ∧
  (S.cubeCount = 2 ↔ (S.params.m : ℕ) + (S.params.K : ℕ) = S.sideExponent + S.level) ∧
  (3 ≤ S.cubeCount ↔ (S.params.m : ℕ) + (S.params.K : ℕ) ≥ S.sideExponent + S.level + 1)
def DataOrdering : Prop :=
  (∀ m' j m K : ℕ, 0 < m → 0 < K →
    (RegionCells.LevelInRange m K m' j ↔ K ≥ j ∧ m + K ≥ m' + j) ∧
    (m + K ≥ m' + j ↔ (m : ℤ) ≥ (m' : ℤ) + j - K) ∧
    (m + K ≥ m' + j ↔ (K : ℤ) ≥ (m' : ℤ) + j - m) ∧
    (K ≥ j → m > m' → m + K ≥ m' + j + 1)) ∧
  ∀ m' j : ℕ, 0 < m' + 1 ∧ 0 < j + 1 ∧ j + 1 ≥ j ∧ m' + 1 > m' ∧
    (m' + 1) + (j + 1) ≥ m' + j + 1
def AdmissibleData : Prop :=
  (∀ S : LevelUnitPartition,
    S.level ≤ (S.params.K : ℕ) ∧
    S.sideExponent + S.level ≤ (S.params.m : ℕ) + (S.params.K : ℕ) ∧
    (3 ≤ S.cubeCount ↔
      S.sideExponent + S.level + 1 ≤ (S.params.m : ℕ) + (S.params.K : ℕ)) ∧
    (S.cubeCount = 2 ↔
      (S.params.m : ℕ) + (S.params.K : ℕ) = S.sideExponent + S.level)) ∧
  (∀ (L m' j : ℕ), Conventions.IsAdmissibleBlockingFactor L →
    ∃ S : LevelUnitPartition, S.params.L = L ∧ S.sideExponent = m' ∧ S.level = j ∧
      3 ≤ S.cubeCount) ∧
  ∀ (s : Conventions.StandingParameters) (m' j : ℕ), m' < (s.m : ℕ) → j ≤ (s.K : ℕ) →
    ∃ S : LevelUnitPartition, S.params = s ∧ S.sideExponent = m' ∧ S.level = j ∧
      3 ≤ S.cubeCount
def SiteAndCubeLifts : Prop :=
  (∀ c : Fin 4 → ℝ,
    (∃ y : Site S.params.L S.params.m S.index, S.IsPointLift (y : S.Points) c) ↔
      IsCubeCentre S c) ∧
  (∀ (y : Site S.params.L S.params.m S.index) (c : Fin 4 → ℝ),
    S.IsPointLift (y : S.Points) c → cubeAround y = S.proj '' S.closedBox c) ∧
  (∀ y y' : Site S.params.L S.params.m S.index, y ≠ y' → cubeAround y ≠ cubeAround y') ∧
  S.cubes.Finite
def VertexAndEdgeLifts : Prop :=
  (∀ v : S.Points, S.IsVertex v ↔ ∃ w ∈ S.vertexSet, v = S.proj w) ∧
  (∀ (v : S.Points) (w : Fin 4 → ℝ), S.IsVertex v → S.IsPointLift v w → w ∈ S.vertexSet) ∧
  (∀ e : Set S.Points, S.IsEdge e ↔ ∃ w ∈ S.vertexSet, ∃ ν, e = S.edgeAt w ν) ∧
  {v : S.Points | S.IsVertex v}.Finite ∧
  {e : Set S.Points | S.IsEdge e}.Finite ∧
  ∀ c : Fin 4 → ℝ, IsCubeCentre S c →
    S.closedBox c ∩ S.vertexSet =
      {x | ∃ ε, LevelUnitPartition.IsSigns ε ∧ x = c + ((S.side : ℝ) / 2) • ε}
def EdgePointsInCube : Prop :=
  ∀ (c w : Fin 4 → ℝ) (ν : Fin 4) (t : ℝ), IsCubeCentre S c → w ∈ S.vertexSet →
    0 ≤ t → t ≤ (S.side : ℝ) → w + t • coordVec ν ∈ S.closedBox c →
    (w ∈ S.closedBox c ∨ w + (S.side : ℝ) • coordVec ν ∈ S.closedBox c) ∧
    (0 < t → t < (S.side : ℝ) →
      (∃ ε, LevelUnitPartition.IsSigns ε ∧ ε ν = -1 ∧
        w = c + ((S.side : ℝ) / 2) • ε) ∧
      S.IsEdgeOf (S.edgeAt w ν) (S.proj '' S.closedBox c))
def ShortVectorsNotPeriods : Prop :=
  (∀ r : Fin 4 → ℝ, r ≠ 0 →
    (∀ μ, r μ = 0 ∨ r μ = (S.side : ℝ) ∨ r μ = -(S.side : ℝ)) → ¬ IsPeriodVector S r) ∧
  (3 ≤ S.cubeCount → ∀ r : Fin 4 → ℝ, r ≠ 0 →
    (∀ μ, r μ = 0 ∨ r μ = (S.side : ℝ) ∨ r μ = -(S.side : ℝ) ∨
      r μ = 2 * (S.side : ℝ) ∨ r μ = -(2 * (S.side : ℝ))) → ¬ IsPeriodVector S r)
def Statement : Prop :=
  DataOrdering ∧ AdmissibleData ∧
  ∀ S : LevelUnitPartition,
    TorusInCubeUnits S ∧ CubeCountDichotomy S ∧ SiteAndCubeLifts S ∧
      VertexAndEdgeLifts S ∧ EdgePointsInCube S ∧ ShortVectorsNotPeriods S
end YangMills.Construction.PeriodicLattice.CubeLifts
end
