import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps TorusFields WeightedResponses CellWindows
def hullRareAtSiteStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N],
    N = 2 * (Tb.stepParameters y).side ^ e → IsTowerAtParameters Tb y T β k → T.MarksMeasurable →
    2 * baseCellSide (Tb.stepParameters y).side (clusterRange (T.stage k).coupling) ≤ N → ∀ v : TorusSite N,
      (markedSampleLaw T β k N).real {u | v ∈ (stageState T k N u).2.1} ≤
        Real.exp (-((T.stage k).coupling * (Tb.stepParameters y).κ₁ * (Tb.stepParameters y).threshold ^ 2 / 2 ^ 5))
end YangMills.Construction.ResponseInTheExpansion
end
