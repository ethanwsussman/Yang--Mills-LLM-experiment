import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def leadingResponseMomentsStatement : Prop :=
  ForAllHullPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ B : Finset (Fin Λ.k),
    Integrable (fun w => ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
    |S.scaleCoupling ^ B.card * ∫ w, ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) -
      ∫ w, Set.indicator {w | S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated)
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).2.1}
        (fun w => S.formProduct S.lastSeparated (S.levelSide S.lastSeparated) B
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated)
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)) w
        ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))| ≤
      C 0 * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)
end YangMills.Construction.MomentLaw
end
