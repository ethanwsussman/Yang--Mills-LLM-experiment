import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.InfiniteLattice.ColumnOverACell
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace timeAxis halfSpacingTimes positiveMultiples timeStep
  timeReflect)
namespace ChessboardTori
namespace ChessboardSetup
def toReflectionSetup (D : ChessboardSetup) : MultipleReflections.Setup :=
  ⟨D.toStandingParameters, D.β, D.beta_pos⟩
end ChessboardSetup
namespace GridCell
variable {D : ChessboardSetup} (c : GridCell D)
def stackGrid : D.toReflectionSetup.Grid :=
  ⟨c.side, c.hasAdmissibleSide, c.origin, c.grid.origin_mem⟩
theorem stackGrid_tileCenter : c.stackGrid.tileCenter c.index = c.centre := by
  funext μ
  have hsum : (∑ ν, InfiniteLattice.ReflectionGrid.basisVec ν : AmbientSpace) μ = 1 := by
    simp [InfiniteLattice.ReflectionGrid.basisVec, Finset.sum_apply, Pi.single_apply]
  simp only [InfiniteLattice.ReflectionGrid.tileCenter, InfiniteLattice.ReflectionGrid.cornerAt,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsum, mul_one]
  rfl
theorem stackGrid_tile : c.stackGrid.tile c.index = c.cell := by
  ext x
  refine forall_congr' fun μ => ?_
  have h : c.stackGrid.cornerAt c.index μ = c.grid.origin μ + c.grid.cellSide * c.index μ := rfl
  rw [h]
  change _ ↔ x μ - (c.grid.origin μ + c.grid.cellSide * c.index μ) ∈ Set.Icc 0 c.grid.cellSide
  have hs : c.stackGrid.edge = c.grid.cellSide := rfl
  rw [hs, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
theorem stackGrid_baseTime : c.stackGrid.baseTime c.index = c.bottomTime := by
  have hs : c.stackGrid.edge = c.side := rfl
  rw [MultipleReflections.Setup.Grid.baseTime, c.stackGrid_tileCenter, hs, bottomTime]
  ring
def baseLevel : halfSpacingTimes D.mesh := c.stackGrid.wallTimeHalf c.index 0
theorem baseLevel_coe : (c.baseLevel : ℝ) = c.bottomTime :=
  (c.stackGrid.wallTimeHalf_zero c.index).trans c.stackGrid_baseTime
def sideMultiple : positiveMultiples D.mesh := c.stackGrid.edgeMultiple
theorem sideMultiple_coe : (c.sideMultiple : ℝ) = c.side := rfl
end GridCell
end ChessboardTori
end YangMills.Construction
end
