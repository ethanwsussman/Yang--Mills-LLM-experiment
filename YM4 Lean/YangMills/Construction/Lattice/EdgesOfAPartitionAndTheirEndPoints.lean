import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties in
def PartitionEdgeEndpoints : Prop :=
  ∀ (S : LevelUnitPartition) (X : Set S.Points), IsPartitionRegion S.index X →
      EdgeEndpointFacts S X
end YangMills.Construction.PeriodicLattice
end
