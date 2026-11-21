import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
def ScalingPreservesCellsAndGroup : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D) (g : ReflectionGrid D), g.HasAdmissibleSide →
    S.PreservesCellsAndGroup g
end YangMills.Construction.MirrorGridsAllSides
end
