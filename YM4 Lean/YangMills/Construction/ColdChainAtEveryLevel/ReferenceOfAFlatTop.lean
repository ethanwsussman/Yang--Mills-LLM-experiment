import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def flatTopReferenceStatement : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell) (j : ℕ) (x : F.Site j) (i : Fin 4), Odd F.blockSide →
    IsAdmissibleAmbient F → j ≤ F.top →
    enclosingCell x ∈ S → enclosingCell (x + unitStep j i) ∈ S → referenceFieldChain S flatTopField j x i = 1
end YangMills.Construction.BlockAverages
end
