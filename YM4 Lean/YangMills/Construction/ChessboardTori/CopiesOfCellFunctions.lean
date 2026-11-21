import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def CellFunctionCopies.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.TransportRules
end YangMills.Construction.ChessboardTori
end
