import YangMills.Construction.ColdChainAtEveryLevel.ResponseAtAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def shareSecondDerivAtResponseStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ v : F.Site F.top → Fin 4 → imaginaryQuaternions, ∃ U : ChainChart F, IsFlatTopResponse a S v U ∧
        iteratedDeriv 2 (fun τ : ℝ => minimalCellShare a S 0 (rotatedField (fun y i => τ • v y i) flatTopField)) 0 =
          responseCellShare a S 0 (referenceFieldChain S flatTopField) U v
end YangMills.Construction.BlockAverages
end
