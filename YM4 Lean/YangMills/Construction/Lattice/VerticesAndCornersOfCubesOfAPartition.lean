import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def PartitionCubeVertexCornerIncidence : Prop :=
  ∀ (S : LevelUnitPartition) (X : Set S.Points), IsPartitionRegion S.index X →
      VertexCornerIncidence S X
end YangMills.Construction.PeriodicLattice
end
