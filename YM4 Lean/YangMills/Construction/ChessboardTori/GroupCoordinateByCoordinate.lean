import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ReflectionGroupCoordinates.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.ReflectionGroupCoordForm
end YangMills.Construction.ChessboardTori
end
