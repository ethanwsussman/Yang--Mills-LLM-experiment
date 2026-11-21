import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def ProductOnTorusHolds : Prop :=
  ∀ (D : Setup) (G : D.Grid) (h : 2 * G.edge ≤ D.side), ProductLiftsToTorus G h
end YangMills.Construction.MultipleReflections
end
