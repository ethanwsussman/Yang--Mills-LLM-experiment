import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def TorusGroupInducedHolds : Prop :=
  ∀ (D : Setup) (G : D.Grid) (h : 2 * G.edge ≤ D.side) (i : ℕ), TorusGroupInduced G i h
end YangMills.Construction.MultipleReflections
end
