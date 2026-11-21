import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def CubeNeighboursOnThreeWideTorus : Prop :=
  ∀ (S : LevelUnitPartition), CubeNeighboursOfWideTorus S
end YangMills.Construction.PeriodicLattice
end
