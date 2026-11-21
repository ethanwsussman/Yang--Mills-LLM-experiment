import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def TiledIntegralFallsWithPeriods : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S, ∀ n : EvenIndexVector,
      (tiledIntegral g n S F).im = 0 ∧ 0 ≤ (tiledIntegral g n S F).re ∧
      (∀ μ : Fin 4, (tiledIntegral g n S F).re ≤
        (tiledIntegral g (setTwo n μ) S F).re ^ (n.coord μ / 2).toNat) ∧
      (tiledIntegral g n S F).re ≤
        (tiledIntegral g (minimalCounts D) S F).re ^ (cellCount n / 16)
end YangMills.Construction.ReflectedCopies
end
