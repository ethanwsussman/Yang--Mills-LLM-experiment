import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
def ScalingPreservesCellObservables : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D) (g : ReflectionGrid D), g.HasAdmissibleSide →
    S.PreservesCellObservables g
end YangMills.Construction.MirrorGridsAllSides
end
