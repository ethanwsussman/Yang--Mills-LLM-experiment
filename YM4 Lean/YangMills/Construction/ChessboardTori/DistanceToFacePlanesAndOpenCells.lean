import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def WallDistanceAndOpenCells.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.DistToWalls
end YangMills.Construction.ChessboardTori
end
