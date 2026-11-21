import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CellsOfRegionsAndCubesAtALevel
import YangMills.Construction.Lattice.LocalizationDomainsAndEdgeTrees
import YangMills.Construction.PeriodicLattice.LevelProjectionAndLiftedCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
structure LevelUnitPartition where
  params : Conventions.StandingParameters
  sideExponent : ℕ
  level : ℕ
  inRange : RegionCells.LevelInRange params.m params.K sideExponent level
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
abbrev Points : Type := S.params.Torus
def side : ℕ := S.params.L ^ S.sideExponent
def index : ℤ := coarseCubeIndex S.params.K S.sideExponent S.level
def cubeCount : ℕ := 2 * S.params.L ^ ((S.params.m : ℤ) + S.index).toNat
def cubes : Set (Set S.Points) :=
  RegionCells.partitionAtLevel S.params.L S.params.m S.params.K S.sideExponent S.level
def IsPointLift (x : S.Points) (w : Fin 4 → ℝ) : Prop :=
  IsLevelLift S.params.L S.params.m S.params.K S.level x w
def proj (w : Fin 4 → ℝ) : S.Points :=
  levelProj S.params.L S.params.m S.params.K S.level w
def segmentBetween (x x' : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (x' - x)}
def IsEuclideanSegment (σ : Set (Fin 4 → ℝ)) : Prop := ∃ x x', σ = segmentBetween x x'
def IsSegmentEndpoint (σ : Set (Fin 4 → ℝ)) (z : Fin 4 → ℝ) : Prop :=
  ∃ x x', σ = segmentBetween x x' ∧ (z = x ∨ z = x')
def IsSegmentLift (σ : Set S.Points) (σ' : Set (Fin 4 → ℝ)) : Prop :=
  IsEuclideanSegment σ' ∧ σ = S.proj '' σ'
def IsTorusSegment (σ : Set S.Points) : Prop := ∃ σ', S.IsSegmentLift σ σ'
def vertexSet : Set (Fin 4 → ℝ) :=
  {w | ∀ μ, ∃ a : ℤ, w μ = (S.side : ℝ) * ((a : ℝ) + 1 / 2)}
def closedBox (c : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∀ μ, x μ ∈ Icc (c μ - (S.side : ℝ) / 2) (c μ + (S.side : ℝ) / 2)}
def edgeAt (w : Fin 4 → ℝ) (ν : Fin 4) : Set S.Points :=
  S.proj '' {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ (S.side : ℝ) ∧ x = w + t • coordVec ν}
def facetAt (c : Fin 4 → ℝ) (ν : Fin 4) (σ : ℝ) : Set S.Points :=
  S.proj '' {x | x ∈ S.closedBox c ∧ x ν = c ν + σ * (S.side : ℝ) / 2}
def IsSigns (ε : Fin 4 → ℝ) : Prop := ∀ μ, ε μ = 1 ∨ ε μ = -1
def IsCornerOf (v : S.Points) (Δ : Set S.Points) : Prop :=
  ∃ y : Site S.params.L S.params.m S.index, Δ = cubeAround y ∧
    ∃ c, S.IsPointLift (y : S.Points) c ∧ ∃ ε, IsSigns ε ∧
      v = S.proj (c + ((S.side : ℝ) / 2) • ε)
def IsEdgeOf (e Δ : Set S.Points) : Prop :=
  ∃ y : Site S.params.L S.params.m S.index, Δ = cubeAround y ∧
    ∃ c, S.IsPointLift (y : S.Points) c ∧ ∃ ε ν, IsSigns ε ∧ ε ν = -1 ∧
      e = S.edgeAt (c + ((S.side : ℝ) / 2) • ε) ν
def IsVertex (v : S.Points) : Prop := ∃ Δ ∈ S.cubes, S.IsCornerOf v Δ
def IsEdge (e : Set S.Points) : Prop := ∃ Δ ∈ S.cubes, S.IsEdgeOf e Δ
def IsEdgeEndpoint (e : Set S.Points) (v : S.Points) : Prop :=
  ∃ w ∈ S.vertexSet, ∃ ν, e = S.edgeAt w ν ∧
    (v = S.proj w ∨ v = S.proj (w + (S.side : ℝ) • coordVec ν))
def Adjacent (v v' : S.Points) : Prop :=
  S.IsVertex v ∧ S.IsVertex v' ∧ v ≠ v' ∧
    ∃ e, S.IsEdge e ∧ S.IsEdgeEndpoint e v ∧ S.IsEdgeEndpoint e v'
def IsConnectedVertices (W : Set S.Points) : Prop :=
  (∀ v ∈ W, S.IsVertex v) ∧ W.Nonempty ∧ ∀ v ∈ W, ∀ v' ∈ W,
    ∃ c : List S.Points, (∀ u ∈ c, u ∈ W) ∧ c.IsChain S.Adjacent ∧
      c.head? = some v ∧ c.getLast? = some v'
def fullRegion : Set S.Points := ⋃₀ S.cubes
def IsEdgeGraphInRegion (X Γ : Set S.Points) : Prop := PeriodicLattice.IsEdgeGraph S.index X Γ
def IsEdgeTreeInRegion (X Γ : Set S.Points) : Prop := PeriodicLattice.IsEdgeTree S.index X Γ
def IsGlobalEdgeGraph (Γ : Set S.Points) : Prop := S.IsEdgeGraphInRegion S.fullRegion Γ
def IsGlobalEdgeTree (Γ : Set S.Points) : Prop := S.IsEdgeTreeInRegion S.fullRegion Γ
def graphEdges (Γ : Set S.Points) : Set (Set S.Points) := {e | S.IsEdge e ∧ e ⊆ Γ}
def graphVertices (Γ : Set S.Points) : Set S.Points :=
  {v | (∃ e ∈ S.graphEdges Γ, S.IsEdgeEndpoint e v) ∨ (S.IsVertex v ∧ Γ = {v})}
def cubesContaining (v : S.Points) : Set (Set S.Points) := {Δ | Δ ∈ S.cubes ∧ v ∈ Δ}
def cubesMeeting (W : Set S.Points) : Set (Set S.Points) := ⋃ v ∈ W, S.cubesContaining v
end LevelUnitPartition
end PeriodicLattice
end YangMills.Construction
