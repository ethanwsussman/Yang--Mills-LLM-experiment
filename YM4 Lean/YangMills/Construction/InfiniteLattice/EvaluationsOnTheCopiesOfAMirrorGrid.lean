import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def LiftsCommuteHolds : Prop :=
  ∀ (D : Setup) (G : D.Grid), 2 * G.edge ≤ D.side → LiftsCommuteWithCopies G
end YangMills.Construction.MultipleReflections
end
