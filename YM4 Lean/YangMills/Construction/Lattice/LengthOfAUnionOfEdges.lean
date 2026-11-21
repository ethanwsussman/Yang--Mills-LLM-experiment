import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
def edgeSegmentSet (w : Fin 4 → ℝ) (ν : Fin 4) : Set (Fin 4 → ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ (S.side : ℝ) ∧ x = w + t • coordVec ν}
def edgeSegment (w : Fin 4 → ℝ) (ν : Fin 4) : TorusMetric.LiftedSegment :=
  ⟨w, w + (S.side : ℝ) • coordVec ν⟩
def degenerateSegment (z : Fin 4 → ℝ) : TorusMetric.LiftedSegment := ⟨z, z⟩
def EnumeratesEdges (𝒜 : Set (Set S.Points)) (l : List ((Fin 4 → ℝ) × Fin 4)) : Prop :=
  (∀ p ∈ l, p.1 ∈ S.vertexSet) ∧ (l.map fun p => S.edgeAt p.1 p.2).Nodup ∧
    ∀ e, e ∈ 𝒜 ↔ e ∈ l.map fun p => S.edgeAt p.1 p.2
def edgeSegments (l : List ((Fin 4 → ℝ) × Fin 4)) : List TorusMetric.LiftedSegment :=
  l.map fun p => S.edgeSegment p.1 p.2
def levelL1Norm (x : S.Points) : ℝ :=
  toLevelUnits S.params.L S.params.K S.level (TorusMetric.torusL1Norm x)
end LevelUnitPartition
def EdgeUnionLength : Prop :=
  ∀ S : LevelUnitPartition,
    (∀ w ∈ S.vertexSet, ∀ ν : Fin 4,
      S.IsTorusSegment (S.edgeAt w ν) ∧
      S.IsSegmentLift (S.edgeAt w ν) (S.edgeSegmentSet w ν) ∧
      (∀ z, LevelUnitPartition.IsSegmentEndpoint (S.edgeSegmentSet w ν) z ↔
        z = w ∨ z = w + (S.side : ℝ) • coordVec ν) ∧
      (S.edgeSegment w ν).displacement = (S.side : ℝ) • coordVec ν ∧
      TorusMetric.l1NormVec (S.edgeSegment w ν).displacement = (S.side : ℝ) ∧
      S.levelL1Norm (S.proj (S.edgeSegment w ν).displacement) = (S.side : ℝ)) ∧
    (∀ 𝒜 : Set (Set S.Points), 𝒜.Finite → (∀ e ∈ 𝒜, S.IsEdge e) → 1 ≤ 𝒜.ncard →
      (∃ l, S.EnumeratesEdges 𝒜 l) ∧
        ∀ l, S.EnumeratesEdges 𝒜 l →
          TorusMetric.pathLength (S.edgeSegments l) = (S.side : ℝ) * (𝒜.ncard : ℝ)) ∧
    (∀ x : S.Points,
      S.IsTorusSegment {x} ∧ (∃ z, S.IsPointLift x z) ∧
      ∀ z, S.IsPointLift x z →
        S.IsSegmentLift {x} (LevelUnitPartition.segmentBetween z z) ∧
        (∀ u, LevelUnitPartition.IsSegmentEndpoint (LevelUnitPartition.segmentBetween z z) u ↔
          u = z) ∧
        TorusMetric.pathLength [LevelUnitPartition.degenerateSegment z] = 0 ∧
        S.levelL1Norm (S.proj 0) = 0)
end PeriodicLattice
end YangMills.Construction
