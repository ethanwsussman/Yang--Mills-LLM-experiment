import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def ChessboardObjectsHold : Prop :=
  ∀ (D : Setup) (G : D.Grid), ChessboardObjectsAgree G
end YangMills.Construction.MultipleReflections
end
