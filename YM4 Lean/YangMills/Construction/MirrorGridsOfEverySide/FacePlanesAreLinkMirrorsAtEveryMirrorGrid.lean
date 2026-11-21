import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
def AllGridsWallsBisectLinks : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → WallsBisectLinks g
end MirrorGridsAllSides
end YangMills.Construction
end
