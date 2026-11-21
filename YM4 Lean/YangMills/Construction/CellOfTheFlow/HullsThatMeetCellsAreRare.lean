import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses BlockAverages LumpContours
def hullMeetsCellsBoundStatement : Prop :=
  ∃ C₁ C₂ : ParameterAssignment → ℝ, HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k →
    ∀ (e : ℕ) (G : CellGrid) (κ : Fin 4 → ℤ) (S : Finset (Fin 4 → ℤ)),
      G.side = baseCellSide (Tb.stepParameters y).side (stageRange T k) →
      2 * G.side ≤ 2 * (Tb.stepParameters y).side ^ e →
      S ⊆ G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ →
      markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)
          {u | ∀ κ' ∈ S, (stageHull T k _ u ∩
            interiorAtDepth (8 * stageRange T k) (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')).Nonempty} ≤
        ENNReal.ofReal (Real.exp ((C₁ Tb + C₂ Tb * Real.log (T.stage k).coupling) *
            (2 * ((Tb.stepParameters y).side : ℝ) ^ e) ^ 4 -
          (T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2 * S.card))
end YangMills.Construction.CellWindows
end
