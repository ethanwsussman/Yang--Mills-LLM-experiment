import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def PartitionCubeNeighbours : Prop :=
  ∀ (S : LevelUnitPartition),
      CubeNeighbours S
end YangMills.Construction.PeriodicLattice
end
