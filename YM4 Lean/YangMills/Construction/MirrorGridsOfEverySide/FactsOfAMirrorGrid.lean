import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
def ReflectionGridProperties : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    CellSideOddMultiple g ∧
    WallsBisectLinks g ∧
    CellCentresInLattice g ∧
    ReflectionGroupActsOnCells g ∧
    ActsOnCellObservables g ∧
    TransportLaws g ∧
    (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      TorusCellStructure g ∧
      TorusGroupActsOnCells g ∧
      TorusWallReflections g ∧
      TorusActsOnCellObservables g ∧
      TorusTransportLaws g ∧
      LiftCompatibleWithTransport g ∧
      WallPreservingSymmetries g) ∧
    (∀ (h : ReflectionGrid D) (n : ℕ), h.IsCoarsening g → h.cellSide = (D.L : ℝ) ^ n * g.cellSide →
      CoarseningOnSpace g h n ∧
      (2 * h.cellSide ≤ PeriodicLattice.torusSide D.L D.m → CoarseningOnTorus g h n)) ∧
    FiniteCellsInCoarserCell g
end MirrorGridsAllSides
end YangMills.Construction
end
