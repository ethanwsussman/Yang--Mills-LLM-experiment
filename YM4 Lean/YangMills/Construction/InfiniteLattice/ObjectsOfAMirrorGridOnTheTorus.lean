import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open Setup.Grid in
def TorusGridObjectsAgree : Prop :=
  ∀ (D : Setup) (G : D.Grid) (h : 2 * G.edge ≤ D.side),
    ChessboardObjectsAgree G ∧
    LiftsCommuteWithCopies G ∧
    ProductLiftsToTorus G h ∧
    EstimateNormAgrees G ∧
    ∀ i : ℕ, GluingObjectsAgree G i h ∧ TorusCellsEqImages G i h ∧
      TorusGroupInduced G i h ∧ GluingNormAgrees G i h
end YangMills.Construction.MultipleReflections
end
