import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid)
def CellSideOddMultipleEveryGrid : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → CellSideOddMultiple g
end YangMills.Construction.MirrorGridsAllSides
end
