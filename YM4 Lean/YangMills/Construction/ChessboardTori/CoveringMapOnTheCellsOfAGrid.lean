import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ProjOnGridCells.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m → g.ProjOnCellsAndBlocks
end YangMills.Construction.ChessboardTori
end
