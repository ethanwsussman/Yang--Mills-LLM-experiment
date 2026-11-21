import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
def EdgeGraphsExtendToLargerRegions : Prop :=
  ∀ S : LevelUnitPartition,
    (∀ X Y : Set S.Points, IsPartitionRegion S.index X → IsPartitionRegion S.index Y →
      partitionCubesIn S.index X ⊆ partitionCubesIn S.index Y →
        (∀ Γ : Set S.Points, Γ.Nonempty → S.IsEdgeGraphInRegion X Γ → S.IsEdgeGraphInRegion Y Γ) ∧
        (∀ Γ : Set S.Points, S.IsEdgeTreeInRegion X Γ → S.IsEdgeTreeInRegion Y Γ)) ∧
    (∀ X : Set S.Points, IsPartitionRegion S.index X →
      (∀ Γ : Set S.Points, Γ.Nonempty → S.IsEdgeGraphInRegion X Γ → S.IsGlobalEdgeGraph Γ) ∧
      (∀ Γ : Set S.Points, S.IsEdgeTreeInRegion X Γ → S.IsGlobalEdgeTree Γ))
end YangMills.Construction.PeriodicLattice
