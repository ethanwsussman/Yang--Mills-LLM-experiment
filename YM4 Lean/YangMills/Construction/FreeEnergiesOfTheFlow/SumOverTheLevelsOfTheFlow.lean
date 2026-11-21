import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open RenormalizationStepParameters TorusLumps ClusterExpansionOfAStep WeightedResponses
def levelSumBoundStatement : Prop :=
  AtResponseParameters fun Tb _ y => ∀ (β : ℝ) (tp : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β tp →
    ∀ w ≤ tp,
    ∑ u ∈ Finset.Ico w tp, Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β u)) ≤ 1 ∧
    ∑ u ∈ Finset.Ico w tp, Real.exp (-(8 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β u)) ≤ 1
end YangMills.Construction.FreeEnergies
end
