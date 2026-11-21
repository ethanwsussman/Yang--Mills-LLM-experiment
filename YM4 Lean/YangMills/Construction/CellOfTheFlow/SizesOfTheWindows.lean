import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open WeightedResponses
def windowDepthBoundStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k →
    (∀ j ≤ k, (windowDepth T k j : ℝ) ≤ (stageRange T j : ℝ) * (7 + 2⁻¹ ^ 20 * ((k : ℝ) - j))) ∧
      windowDepth T k k ≤ 8 * stageRange T k
end YangMills.Construction.CellWindows
end
