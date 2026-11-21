import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def GluingNormHolds : Prop :=
  ∀ (D : Setup) (G : D.Grid) (h : 2 * G.edge ≤ D.side) (i : ℕ), GluingNormAgrees G i h
end YangMills.Construction.MultipleReflections
end
