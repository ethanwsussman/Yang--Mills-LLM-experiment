import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def ScalingPreservesGridPoints : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D), S.PreservesGridPoints
end YangMills.Construction.MirrorGridsAllSides
end
