import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def ScalingPreservesMeasures : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D), S.PreservesMeasures
end YangMills.Construction.MirrorGridsAllSides
end
