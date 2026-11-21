import YangMills.Construction.InfiniteLattice.ArrayOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.CellsOfTheTorusOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.ChessboardObjectsOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.ChessboardValueOfTheEstimate
import YangMills.Construction.InfiniteLattice.ChessboardValueOfTheSourcesPart
import YangMills.Construction.InfiniteLattice.EvaluationsOnTheCopiesOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.InducedGroupOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.SourcesObjectsOfAMirrorGrid
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.MultipleReflections
theorem torusGridObjectsAgree_of
    (hChessboard : ChessboardObjectsHold)
    (hLiftsCommute : LiftsCommuteHolds)
    (hArray : ProductOnTorusHolds)
    (hEstimate : EstimateNormHolds)
    (hSources : GluingGridObjectsAgree)
    (hCells : TorusCellsHold)
    (hGroup : TorusGroupInducedHolds)
    (hValue : GluingNormHolds) :
    TorusGridObjectsAgree :=
  fun D G h => ⟨hChessboard D G, hLiftsCommute D G h, hArray D G h, hEstimate D G h,
    fun i => ⟨hSources D G h i, hCells D G h i, hGroup D G h i, hValue D G h i⟩⟩
end YangMills.Construction.MultipleReflections
