import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def longSupportsConditionalBoundStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j d : ℕ),
    IsTowerAtParametersMeasurable Tb y T β (j + 1 + d) →
    ∀ (e : ℕ) (G : CellGrid) (κ : Fin 4 → ℤ) (S : Finset (Fin 4 → ℤ)),
      G.side = baseCellSide (Tb.stepParameters y).side (stageRange T (j + 1 + d)) →
      2 * G.side ≤ 2 * (Tb.stepParameters y).side ^ e →
      S ⊆ G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ →
      ∀ A : Set (MarkedSample (Tb.stepParameters y) (j + 1)
          (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e))),
        MeasurableSet[stageSigma T (j + 1)
          (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e))] A →
        markedSampleLaw T β (j + 1) (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e))
            (A ∩ {v | ∀ κ' ∈ S, HasLongSupport T (j + 1 + d) j (j + 1) _ v
              (cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
                (G.cell (2 * (Tb.stepParameters y).side ^ e) κ'))}) ≤
          ENNReal.ofReal (Real.exp (-(8 * Tb.gasRate * (T.stage j).coupling * (100 * ((d : ℝ) + 1)) * S.card))) *
            markedSampleLaw T β (j + 1)
              (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)) A
end YangMills.Construction.CellWindows
end
