import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ExponentialObservableRules.Statement : Prop :=
  ∀ D : ChessboardSetup, D.ExpSmearedRules
end YangMills.Construction.ChessboardTori
end
