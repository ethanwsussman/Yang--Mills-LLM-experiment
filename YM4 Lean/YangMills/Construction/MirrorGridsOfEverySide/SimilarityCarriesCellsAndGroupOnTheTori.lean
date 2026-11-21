import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
def ScalingPreservesCellsAndGroupTorus : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D) (g : ReflectionGrid D), g.HasAdmissibleSide →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    S.PreservesCellsAndGroupTorus g
end YangMills.Construction.MirrorGridsAllSides
end
