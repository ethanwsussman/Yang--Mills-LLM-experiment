import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def EdgeGraphsMeetCubesAtVertices : Prop :=
  ∀ (S : LevelUnitPartition) (X Γ : Set S.Points), IsPartitionRegion S.index X →
    S.IsEdgeGraphInRegion X Γ → Γ.Nonempty →
      MeetsGraphAtVertices S Γ
end YangMills.Construction.PeriodicLattice
end
