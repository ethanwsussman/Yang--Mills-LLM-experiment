import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
structure CoupledGrid extends ChessboardSetup where
  grid : ReflectionGrid toChessboardSetup
  isCoarse : grid.IsCoarse
namespace CoupledGrid
variable (O : CoupledGrid)
def cellSide : ℝ := O.grid.cellSide
def withExponent (m' : ℕ+) : CoupledGrid :=
  ⟨O.toChessboardSetup.withExponent m', O.grid.withExponent m', O.isCoarse⟩
end CoupledGrid
end ChessboardTori
end YangMills.Construction
end
