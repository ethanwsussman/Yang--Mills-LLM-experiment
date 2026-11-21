import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def PointsOffWalls.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.PointsOffWallsAndSyms
end YangMills.Construction.ChessboardTori
end
