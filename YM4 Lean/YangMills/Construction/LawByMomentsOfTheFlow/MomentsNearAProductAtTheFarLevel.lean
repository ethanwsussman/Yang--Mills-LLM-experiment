import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def productApproxAtLastSeparatedStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => ∀ B : Finset (Fin Λ.k),
    (∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
      |WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated (S.levelSide S.lastSeparated)
          (fun i => S.weight i _) B (fun i => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) w -
          ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
        S.separationError (C B.card) S.lastSeparated B *
          ∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) ∧
    S.separationError (C B.card) S.lastSeparated B ≤ C 100 * ∑ u ∈ Finset.range S.lastSeparated,
      (Λ.stepParams.side : ℝ) ^ (C 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ))) *
      Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) ∧
    (X₀ ≤ S.scaleCoupling → S.separationError (C B.card) S.lastSeparated B ≤ Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200))))
end YangMills.Construction.MomentLaw
end
