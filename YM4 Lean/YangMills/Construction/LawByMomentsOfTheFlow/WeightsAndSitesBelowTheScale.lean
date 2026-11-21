import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses
def weightsSitesBelowScaleStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
    weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1 ∧
      ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤
        C 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))
end YangMills.Construction.MomentLaw
end
