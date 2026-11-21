import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def gridCellCentre {D : ChessboardTori.ChessboardSetup} (c : ChessboardTori.GridCell D) : Fin 4 → ℝ :=
  fun μ => c.grid.origin μ + c.side * (c.index μ : ℝ) + c.side / 2
def recentredAt {D : ChessboardTori.ChessboardSetup} (c : ChessboardTori.GridCell D)
    (f : InfiniteLattice.AmbientSpace → ℝ) : TestFunctions.EuclideanFourSpace → ℝ :=
  fun x => f fun μ => gridCellCentre c μ + x μ
def tiledMeanEqReflectedMeanStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (D : ChessboardTori.ChessboardSetup) (c : ChessboardTori.GridCell D) (κ j : ℕ)
    (f : InfiniteLattice.AmbientSpace → ℝ) (e : ℝ)
    (z : TorusFields.TorusSite (twoCellSide L j 0 * L ^ κ)), D.L = L → (κ : ℤ) = c.grid.q + ((D.K : ℕ) : ℤ) →
    (∀ x, f x ≠ 0 → x ∈ interior c.cell) →
    (∀ μ, ∃ i : ℤ, z μ = (i : ZMod (twoCellSide L j 0 * L ^ κ)) ∧ D.mesh * (i : ℝ) = gridCellCentre c μ) →
    ReflectedCopies.tiledMean c.grid (ReflectedCopies.cubicCounts D j) c.cell
        (ReflectedCopies.centredSmeared D f e) =
      ((reflectedProductMean D.β D.mesh (L ^ κ) (twoCellSide L j 0) z (recentredAt c f) e : ℝ) : ℂ)
end YangMills.Construction.SmallTorusCopies
end
