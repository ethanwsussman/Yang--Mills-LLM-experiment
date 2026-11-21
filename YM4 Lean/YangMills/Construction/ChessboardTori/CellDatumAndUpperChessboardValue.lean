import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.InfiniteLattice.TimeReflections
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
structure GridCell (D : ChessboardSetup) where
  grid : ReflectionGrid D
  hasAdmissibleSide : grid.HasAdmissibleSide
  index : Fin 4 → ℤ
namespace GridCell
variable {D : ChessboardSetup} (c : GridCell D)
def side : ℝ := c.grid.cellSide
def origin : AmbientSpace := c.grid.origin
def cell : Set AmbientSpace := c.grid.cell c.index
theorem cell_mem_cellSet : c.cell ∈ c.grid.cellSet := ⟨c.index, rfl⟩
def centre : AmbientSpace := c.grid.cellCentre c.index
def bottomTime : ℝ := c.centre InfiniteLattice.timeAxis - c.side / 2
def IsAdmissibleSideSequence (m : ℕ+ → ℕ+) : Prop :=
  (∀ r, 2 * c.side ≤ PeriodicLattice.torusSide D.L (m r)) ∧
    Tendsto (fun r => PeriodicLattice.torusSide D.L (m r)) atTop atTop
def chessboardNormAt (m : ℕ+ → ℕ+) (F : D.GaugeField → ℂ) (r : ℕ+) : ℝ :=
  (c.grid.withExponent (m r)).chessboardNormOfCell c.cell F
def limsupChessboardNorm (m : ℕ+ → ℕ+) (_hm : c.IsAdmissibleSideSequence m) (F : D.GaugeField → ℂ)
    (_hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell) : ℝ :=
  limsup (c.chessboardNormAt m F) atTop
end GridCell
end ChessboardTori
end YangMills.Construction
end
