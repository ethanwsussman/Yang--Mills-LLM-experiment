import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def GridBasicProperties.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    g.PointsOffWallsAndSyms ∧ D.LatticeSymMapsLinksFaces ∧
    D.ExpSmearedRules ∧ g.ReflectionGroupCoordForm ∧ g.TransportRules ∧
    g.DistToWalls ∧
    (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      g.DescendsToTorus ∧ g.TorusGroupQuotient ∧ g.ProjOnCellsAndBlocks)
end YangMills.Construction.ChessboardTori
end
