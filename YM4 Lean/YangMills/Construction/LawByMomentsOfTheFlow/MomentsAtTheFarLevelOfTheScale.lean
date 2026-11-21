import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def separatedLevelMomentsStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ (B : Finset (Fin Λ.k)) (κ : Fin Λ.k → ℝ),
    ∫ w, ∏ i ∈ B, (WeightedResponses.curvatureObservable (S.weight i _)
        (WeightedResponses.bottomField Λ.stepParams S.lastSeparated (S.levelSide S.lastSeparated) w) - κ i)
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) =
      ∫ w, WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated)
        (fun i => S.weight i _) B κ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))
end YangMills.Construction.MomentLaw
end
