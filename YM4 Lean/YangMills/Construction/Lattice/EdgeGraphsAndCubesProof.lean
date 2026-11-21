import YangMills.Construction.Lattice.AdjacentCubesWithThreeCubesInEachDirection
import YangMills.Construction.Lattice.AdjacentVerticesAndConnectedEdgeGraphs
import YangMills.Construction.Lattice.CubesAdjacentToACubeOfAPartition
import YangMills.Construction.Lattice.EdgeGraphsAndCubes
import YangMills.Construction.Lattice.EdgeGraphsMeetCubesAtTheirVertices
import YangMills.Construction.Lattice.EdgesOfAPartitionAndTheirEndPoints
import YangMills.Construction.Lattice.NumberingOfVerticesAlongEdges
import YangMills.Construction.Lattice.VerticesAndCornersOfCubesOfAPartition
import YangMills.Construction.Lattice.VerticesAndCubesOfAConnectedEdgeGraph
import YangMills.Construction.Lattice.VerticesOfAShortestEdgeTree
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem edgeGraphCubeRelations_of_properties
    (h1 : EdgeGraphsMeetCubesAtVertices)
    (h2 : PartitionCubeVertexCornerIncidence)
    (h3 : PartitionCubeNeighbours)
    (h4 : CubeNeighboursOnThreeWideTorus)
    (h5 : ConnectedEdgeGraphVerticesAndCubes)
    (h6 : ShortestEdgeTreeVertexBound)
    (h7 : PartitionEdgeEndpoints)
    (h8 : AdjacentVerticesConnectEdgeGraphs)
    (h9 : VerticesNumberedAlongEdges) :
    EdgeGraphCubeRelations :=
  fun S X Γ hX hΓ hne =>
    ⟨h1 S X Γ hX hΓ hne, h2 S X hX, h3 S, h4 S, h5 S, h6 S X Γ hX hΓ hne, h7 S X hX, h8 S, h9 S⟩
end YangMills.Construction.PeriodicLattice
