import YangMills.Construction.Lattice.LengthOfAUnionOfEdges
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
def edgeCount (Γ : Set S.Points) : ℕ := (S.graphEdges Γ).ncard
end LevelUnitPartition
def EdgeGraphLengthFormula : Prop :=
  ∀ (S : LevelUnitPartition) (Γ : Set S.Points), S.IsGlobalEdgeGraph Γ → Γ.Nonempty →
    (S.graphEdges Γ).Finite ∧
    (S.edgeCount Γ = 0 → ∃ Δ ∈ S.cubes, ∃ v, S.IsCornerOf v Δ ∧ Γ = {v}) ∧
    (1 ≤ S.edgeCount Γ → Γ = ⋃₀ S.graphEdges Γ) ∧
    (1 ≤ S.edgeCount Γ →
      (∃ l, S.EnumeratesEdges (S.graphEdges Γ) l) ∧
        ∀ l, S.EnumeratesEdges (S.graphEdges Γ) l →
          TorusMetric.pathLength (S.edgeSegments l) = (S.side : ℝ) * (S.edgeCount Γ : ℝ)) ∧
    (S.edgeCount Γ = 0 → ∀ x ∈ Γ, (∃ z, S.IsPointLift x z) ∧
      ∀ z, S.IsPointLift x z →
        TorusMetric.pathLength [LevelUnitPartition.degenerateSegment z] =
          (S.side : ℝ) * (S.edgeCount Γ : ℝ)) ∧
    graphLength S.side S.index Γ = S.side * S.edgeCount Γ
end PeriodicLattice
end YangMills.Construction
