import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def freeSupportsConditionalBoundStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j : ℕ),
    IsTowerAtParametersMeasurable Tb y T β (j + 1) →
    ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (Tb.stepParameters y) m →
      ∀ (Θ : Finset (ClusterSupport (Tb.stepParameters y).side m))
        (A : Set (MarkedSample (Tb.stepParameters y) (j + 1) m)),
        MeasurableSet[stageSigma T (j + 1) m] A →
        markedSampleLaw T β (j + 1) m (A ∩ {v | Θ ⊆ freeSupportsAt T j m v}) ≤
          ENNReal.ofReal (∏ θ ∈ Θ, clusterWeight (Tb.stepParameters y).side Tb.gasRate
            (T.stage j).coupling (stageRange T j) θ) *
            markedSampleLaw T β (j + 1) m A
end YangMills.Construction.CellWindows
end
