import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def productApproxAtSeparatedLevelStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t' ≤ S.data.windowLevel,
    (∀ u ≤ t', ∀ i : Fin Λ.k, WeightedResponses.weightNorm Λ.stepParams.side u
      (S.weight i (WeightedResponses.fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1) →
    S.data.SeparatedBelow Λ.stepParams S.β t' → ∀ B : Finset (Fin Λ.k), ∀ᵐ w ∂(S.law t' (S.levelSide t')),
      |WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff t' (S.levelSide t') (fun i => S.weight i _) B
          (fun i => S.kappa t' (S.levelSide t') i) w -
          ∏ i ∈ B, S.supportTotal t' (S.levelSide t') i (S.state t' (S.levelSide t') w)| ≤
        S.separationError (C B.card) t' B * ∏ i ∈ B, S.meanScore t' (S.levelSide t') i (S.state t' (S.levelSide t') w)
end YangMills.Construction.MomentLaw
end
