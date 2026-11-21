import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def longSupportsAllStagesBoundStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k →
    ∀ (e : ℕ) (G : CellGrid) (κ : Fin 4 → ℤ) (S : ℕ → Finset (Fin 4 → ℤ)),
      G.side = baseCellSide (Tb.stepParameters y).side (stageRange T k) →
      2 * G.side ≤ 2 * (Tb.stepParameters y).side ^ e →
      (∀ j < k, S j ⊆ G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ) →
      ∀ A : Set (MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ e)),
        MeasurableSet[stageSigma T k (2 * (Tb.stepParameters y).side ^ e)] A →
        markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)
            (A ∩ {u | ∀ j < k, ∀ κ' ∈ S j, HasLongSupport T k j k _ u
              (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')}) ≤
          ENNReal.ofReal (∏ j ∈ Finset.range k,
              Real.exp (-(8 * Tb.gasRate * (T.stage j).coupling * (100 * ((k : ℝ) - j)) * (S j).card))) *
            markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e) A
end YangMills.Construction.CellWindows
end
