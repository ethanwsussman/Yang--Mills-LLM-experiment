import YangMills.Construction.ChessboardTori.ChessboardEstimate
import YangMills.Construction.ChessboardTori.CouplingAndGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace CoupledGrid
variable (O : CoupledGrid)
def cellChessboardSeminorm (_hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m)
    {S : Set AmbientSpace} (_hS : S ∈ O.grid.cellSet)
    (F : ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) : ℝ :=
  O.grid.chessboardNorm S F
end CoupledGrid
end ChessboardTori
end YangMills.Construction
end
