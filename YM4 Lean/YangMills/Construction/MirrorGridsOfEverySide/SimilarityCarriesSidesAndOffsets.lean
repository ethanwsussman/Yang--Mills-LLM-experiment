import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def ScalingPreservesSidesAndCentres : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D), S.PreservesSidesAndCentres
end YangMills.Construction.MirrorGridsAllSides
end
