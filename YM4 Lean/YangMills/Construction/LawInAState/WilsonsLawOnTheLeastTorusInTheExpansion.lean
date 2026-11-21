import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LawInAState
def unitTorusMomentsViaWeightsStatement : Prop :=
  ∀ (L K k : ℕ) [NeZero L], Odd L → 3 ≤ L → 1 ≤ K → k ≤ K → ∀ (β : ℝ) (n : ℕ)
    (f : Fin n → YangMills.Construction.InfiniteLattice.AmbientSpace → ℝ),
    (∀ i, YangMills.Construction.InfiniteLattice.IsBoundedBorelCompactlySupported (f i)) →
      ∫ U, ∏ i, YangMills.Construction.StateLaws.smearedObservable L K (f i) U
          ∂YangMills.Construction.StateLaws.unitTorusMeasure L K β =
        ∫ W, ∏ i, YangMills.Construction.WeightedResponses.curvatureObservable
            (YangMills.Construction.BoxResponses.unitTorusWeight L K k (f i)) W
          ∂YangMills.Construction.WeightedResponses.wilsonLaw β
            (YangMills.Construction.WeightedResponses.fineSide L k
              (YangMills.Construction.BoxResponses.boxSide L K k))
end YangMills.Construction.LawInAState
end
