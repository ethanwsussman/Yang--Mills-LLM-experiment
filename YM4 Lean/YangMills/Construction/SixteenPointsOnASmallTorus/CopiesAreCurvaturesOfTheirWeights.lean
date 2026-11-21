import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import YangMills.Construction.ReflectionsAndOneInsertion.OneInsertionAtOneCutoff
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedCopiesAsCurvatureStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (D : ChessboardTori.ChessboardSetup) (c : ChessboardTori.GridCell D) (κ j : ℕ)
    (f : InfiniteLattice.AmbientSpace → ℝ) (f' : TestFunctions.EuclideanFourSpace → ℝ)
    (z : TorusFields.TorusSite (twoCellSide L j 0 * L ^ κ)), D.L = L → (κ : ℤ) = c.grid.q + ((D.K : ℕ) : ℤ) →
    (∀ x, f x ≠ 0 → x ∈ interior c.cell) →
    (∀ x, f' x = f fun μ => c.grid.origin μ + c.side * (c.index μ : ℝ) + c.side / 2 + x μ) →
    (∀ μ, ∃ i : ℤ, z μ = (i : ZMod (twoCellSide L j 0 * L ^ κ)) ∧
      D.mesh * (i : ℝ) = c.grid.origin μ + c.side * (c.index μ : ℝ) + c.side / 2) →
    ∃ Ψ : (ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).GaugeConfig →
        TorusFields.TorusField (twoCellSide L j 0 * L ^ κ),
      MeasurePreserving Ψ (ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).haarMeasure
        (TorusFields.fieldHaar (twoCellSide L j 0 * L ^ κ)) ∧
      (∀ U, (ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).wilsonAction U =
        TorusFields.wilsonAction Finset.univ (Ψ U)) ∧
      ∀ U,
        ReflectionsAndOneInsertion.complexSmeared D f
            ((ReflectedCopies.gridPeriods c.grid
              (ReflectedCopies.cubicCounts D j)).liftGaugeField U) =
          ((WeightedResponses.curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun _ => 0) f') (Ψ U) : ℝ) : ℂ) ∧
        ∀ (k : Fin 4 → ℤ) (k' : Fin 4 → ℕ), (∀ μ, (twoCellSide L j 0 : ℤ) ∣ k μ - c.index μ - (k' μ : ℤ)) →
          c.grid.transportTo c.cell (c.grid.cell k) (ReflectionsAndOneInsertion.complexSmeared D f)
              ((ReflectedCopies.gridPeriods c.grid
                (ReflectedCopies.cubicCounts D j)).liftGaugeField U) =
            ((WeightedResponses.curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z k' f') (Ψ U) : ℝ) : ℂ)
end YangMills.Construction.SmallTorusCopies
end
