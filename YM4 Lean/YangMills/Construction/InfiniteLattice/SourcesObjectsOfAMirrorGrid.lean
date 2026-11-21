import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
def GluingGridObjectsAgree : Prop :=
  ∀ (D : Setup) (G : D.Grid) (hfit : 2 * G.edge ≤ D.side) (i : ℕ), G.GluingObjectsAgree i hfit
end YangMills.Construction.MultipleReflections
end
