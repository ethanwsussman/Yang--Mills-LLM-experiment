import YangMills.Construction.Lattice.PropertiesOfEdgeGraphsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties
def EdgeGraphCubeRelations : Prop :=
  ∀ (S : LevelUnitPartition) (X Γ : Set S.Points), IsPartitionRegion S.index X →
    S.IsEdgeGraphInRegion X Γ → Γ.Nonempty →
      MeetsGraphAtVertices S Γ ∧
      VertexCornerIncidence S X ∧
      CubeNeighbours S ∧
      CubeNeighboursOfWideTorus S ∧
      ConnectedGraphVertexCubeBounds S ∧
      ShortestTreeVertexCount S X Γ ∧
      EdgeEndpointFacts S X ∧
      VertexAdjacencyAndConnectivity S ∧
      EdgeNumbering S
end YangMills.Construction.PeriodicLattice
end
