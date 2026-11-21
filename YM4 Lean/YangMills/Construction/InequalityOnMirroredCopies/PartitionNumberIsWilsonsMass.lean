import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def TorusPartitionIsWilsonPartition : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → ∀ (j m : ℕ) [NeZero m],
    (m : ℤ) = (cubicCounts D j).coord 0 * g.cellRatio →
    torusPartition g (cubicCounts D j) = ClusterExpansionOfAStep.wilsonPartition D.β m
end YangMills.Construction.ReflectedCopies
end
