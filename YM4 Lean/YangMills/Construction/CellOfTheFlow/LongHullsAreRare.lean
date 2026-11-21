import YangMills.Construction.CellOfTheFlow.ACellIsRare
import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses
def longHullsRareStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ R : ℝ, 1 ≤ R → ∃ CR : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k → ∀ (e : ℕ),
      2 * baseCellSide (Tb.stepParameters y).side (stageRange T k) ≤ 2 * (Tb.stepParameters y).side ^ e →
      ∀ (y₀ : TorusSite (2 * (Tb.stepParameters y).side ^ e)) (m : ℕ),
        baseCellSide (Tb.stepParameters y).side (stageRange T k) ≤ m →
        markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)
            {u | m < maxDiameterNearBox T k _ u y₀ R} ≤
          ENNReal.ofReal (CR * cellEventBound Tb (T.stage k).coupling ^
            ((m : ℝ) / (320 * baseCellSide (Tb.stepParameters y).side (stageRange T k))))
end YangMills.Construction.CellWindows
end
