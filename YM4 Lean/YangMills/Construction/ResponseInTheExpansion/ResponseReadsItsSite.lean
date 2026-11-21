import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings TorusFields BlockAverages
def chartResponseDependsOnlyOnSite : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.n₀ ≤ n → s.IsAdmissible →
    ∀ (y : TorusSite (n * R.params.side)) (h h' : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      (∀ p, IsPlaquetteAt R.params.side R.depth y p → h p = h' p) → chartResponse A s y h = chartResponse A s y h'
end YangMills.Construction.ResponseInTheExpansion
end
