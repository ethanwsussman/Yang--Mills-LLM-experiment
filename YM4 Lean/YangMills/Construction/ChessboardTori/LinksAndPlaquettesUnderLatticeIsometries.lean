import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def LatticeSymmetryAction.Statement : Prop :=
  ∀ D : ChessboardSetup, D.LatticeSymMapsLinksFaces
end YangMills.Construction.ChessboardTori
end
