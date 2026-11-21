import YangMills.Construction.ChessboardTori.CopiesOfCellFunctions
import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGrid
import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCells
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.ExponentialsOfObservablesOnTheLattice
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotient
import YangMills.Construction.ChessboardTori.InducedIsometriesOfTheTorus
import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.ChessboardTori.SitesOffTheFacePlanes
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ChessboardTori
theorem GridBasicProperties.proof
    (h1 : PointsOffWalls.Statement)
    (h2 : LatticeSymmetryAction.Statement)
    (h3 : ExponentialObservableRules.Statement)
    (h4 : ReflectionGroupCoordinates.Statement)
    (h5 : CellFunctionCopies.Statement)
    (h6 : WallDistanceAndOpenCells.Statement)
    (h7 : TorusInducedSymmetries.Statement)
    (h8 : TorusReflectionGroup.Statement)
    (h9 : ProjOnGridCells.Statement) :
    GridBasicProperties.Statement :=
  fun D g => ⟨h1 D g, h2 D, h3 D, h4 D g, h5 D g, h6 D g,
    fun h => ⟨h7 D g h, h8 D g h, h9 D g h⟩⟩
end YangMills.Construction.ChessboardTori
