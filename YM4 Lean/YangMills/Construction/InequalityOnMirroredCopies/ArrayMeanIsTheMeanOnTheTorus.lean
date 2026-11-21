import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def TiledMeanIsPeriodicExpectation : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → ∀ S ∈ g.cellSet,
    ∀ F ∈ ReflectionGrid.cellObservables (D := D) S, ∀ (m' : ℕ+) (j : ℕ),
      PeriodicLattice.torusSide D.L m' = 2 * (D.L : ℝ) ^ j * g.cellSide →
      (D.withExponent m').periodicExpectation ((g.withExponent m').cellProduct
          ((D.withExponent m').proj '' S) ((D.withExponent m').liftedObservable F)) =
        tiledMean g (cubicCounts D j) S F ∧
      (g.withExponent m').chessboardNormOfCell S F =
        ‖tiledMean g (cubicCounts D j) S F‖ ^ (1 / (cellCount (cubicCounts D j) : ℝ))
end YangMills.Construction.ReflectedCopies
end
