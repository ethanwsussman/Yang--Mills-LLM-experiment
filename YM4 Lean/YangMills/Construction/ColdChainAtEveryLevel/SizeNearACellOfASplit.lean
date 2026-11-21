import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def splitChartNearCellStatement : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell) (R : F.FieldChain) (U Ul Ur : ChainChart F) (δ A B : ℝ) (z : F.Cell),
    z ∈ S → 0 ≤ δ → δ ≤ 1 / 8 → ChartEqOnBonds S U (chartSum Ul Ur) →
    weightedNorm S R Ul (decayWeights F δ 0 0 z) ≤ A → weightedNorm S R Ur (decayWeights F δ 0 0 z) ≤ B →
    localNorm S R U (oneSiteWeights F) z ≤ 2 * A + 2 * B
end YangMills.Construction.BlockAverages
end
