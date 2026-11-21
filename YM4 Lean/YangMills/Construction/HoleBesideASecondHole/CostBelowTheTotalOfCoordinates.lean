import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open BlockAverages
def chartActionLowerBoundStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), 0 ≤ a → Odd F.blockSide →
    ∀ (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top),
      cutEffectiveAction a F.top S V ≤ chartAction a S R U V ∧
      plainBlockEnergy a S (CellTerms.chartFieldTopFixed R U) V ≤ chartAction a S R U V
end YangMills.Construction.LumpContours
end
