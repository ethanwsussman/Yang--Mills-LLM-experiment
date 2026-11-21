import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def ScalingPreservesTorus : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D), S.PreservesTorus
end YangMills.Construction.MirrorGridsAllSides
end
