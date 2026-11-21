import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def ChessboardNormBoundedByMinimalTorus : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → ∀ j : ℕ,
    1 ≤ torusPartitionRatio g j ∧
    ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      ‖tiledMean g (cubicCounts D j) S F‖ ^ (1 / (cellCount (cubicCounts D j) : ℝ)) ≤
        torusPartitionRatio g j * ‖tiledMean g (minimalCounts D) S F‖ ^ (1 / 16 : ℝ)
end YangMills.Construction.ReflectedCopies
end
