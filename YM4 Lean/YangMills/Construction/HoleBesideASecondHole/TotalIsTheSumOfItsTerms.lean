import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages CellTerms
namespace ChainTerms
def chainActionEqSumTermsStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), 0 ≤ a → Odd F.blockSide →
    ∀ (X : F.FieldChain) (k : F.SiteGauge),
    (∀ z, 0 ≤ cellTerms a S X k z) ∧ gaugedChainAction a S X k = ∑ z ∈ S, cellTerms a S X k z
end ChainTerms
end YangMills.Construction
end
