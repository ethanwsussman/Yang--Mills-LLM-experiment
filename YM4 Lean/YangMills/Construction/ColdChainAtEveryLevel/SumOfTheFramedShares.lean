import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def gaugedCellShareSumStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge), IsAdmissibleAmbient F →
    Odd F.blockSide →
    gaugedChainAction a S X k = ∑ Y ∈ S, gaugedCellShare a S Y X k
end YangMills.Construction.BlockAverages
end
