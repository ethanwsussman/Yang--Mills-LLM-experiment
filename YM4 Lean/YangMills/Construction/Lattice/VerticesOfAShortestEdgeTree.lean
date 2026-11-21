import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def ShortestEdgeTreeVertexBound : Prop :=
  ∀ (S : LevelUnitPartition) (X Γ : Set S.Points), IsPartitionRegion S.index X →
    S.IsEdgeGraphInRegion X Γ → Γ.Nonempty →
      ShortestTreeVertexCount S X Γ
end YangMills.Construction.PeriodicLattice
end
