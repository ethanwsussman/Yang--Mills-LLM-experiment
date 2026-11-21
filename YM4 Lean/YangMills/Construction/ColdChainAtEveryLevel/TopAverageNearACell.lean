import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def topAverageLocalBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (S : Finset F.Cell), Odd F.blockSide → 5 ≤ F.blockSide →
    IsAdmissibleAmbient F →
    ∀ (U : ChainChart F) (c : F.Site F.top × Fin 4), c ∈ innerBonds S F.top →
      ‖linearPart (referenceFieldChain S flatTopField) U F.top c.1 c.2‖ ≤
        C * localNorm S (referenceFieldChain S flatTopField) U (fun _ _ => 1) (enclosingCell c.1)
end YangMills.Construction.BlockAverages
end
