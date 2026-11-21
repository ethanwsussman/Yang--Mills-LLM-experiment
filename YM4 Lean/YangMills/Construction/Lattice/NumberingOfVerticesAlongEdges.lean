import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def VerticesNumberedAlongEdges : Prop :=
  ∀ (S : LevelUnitPartition),
      EdgeNumbering S
end YangMills.Construction.PeriodicLattice
end
