import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
def IsEdgeGraphByParts (X Γ : Set S.Points) : Prop :=
  (∃ Q ∈ S.cubes, ∃ c, PeriodicLattice.IsCubeVertex S.index c Q ∧ c ∈ X ∧ Γ = {c}) ∨
    ∃ E : Set (Set S.Points),
      (∀ e ∈ E, e ⊆ X ∧ ∃ Q ∈ S.cubes, PeriodicLattice.IsCubeEdge S.index e Q) ∧ Γ = ⋃₀ E
def IsDescribedByCubes (X : Set S.Points) (G : Set S.Points → Prop) : Prop :=
  (∀ Γ, G Γ → Γ.Nonempty →
    (∃ Δ ∈ partitionCubesIn S.index X, ∃ v, S.IsCornerOf v Δ ∧ Γ = {v}) ∨
      ∃ E : Set (Set S.Points), E.Finite ∧ E.Nonempty ∧
        (∀ e ∈ E, ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ) ∧ Γ = ⋃₀ E) ∧
  (∀ Δ ∈ partitionCubesIn S.index X, ∀ v, S.IsCornerOf v Δ → G {v}) ∧
  (∀ E : Set (Set S.Points), E.Nonempty →
    (∀ e ∈ E, ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ) → G (⋃₀ E))
end LevelUnitPartition
def EdgeGraphsDescribedByCubes : Prop :=
  ∀ (S : LevelUnitPartition) (X : Set S.Points), IsPartitionRegion S.index X →
    S.IsDescribedByCubes X (S.IsEdgeGraphInRegion X) ∧
      S.IsDescribedByCubes X (S.IsEdgeGraphByParts X)
end PeriodicLattice
end YangMills.Construction
