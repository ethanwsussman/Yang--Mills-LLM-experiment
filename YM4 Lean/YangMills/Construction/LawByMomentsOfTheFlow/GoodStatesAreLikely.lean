import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def goodConfigsLikelyStatement : Prop :=
  ForAllHullPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    (∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + S.logIndex + 1 →
      (∀ N : ℕ, S.law u (S.levelSide u) {w | ¬ S.IsGoodConfig u (S.levelSide u)
          (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1} ≤
        ENNReal.ofReal (C N * S.scaleCoupling ^ (-(N : ℝ)))) ∧
      ∀ k : ℕ, ∫⁻ w, Set.indicator {w | S.IsGoodConfig u (S.levelSide u)
          (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1}
          (fun w => ENNReal.ofReal ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
            S.localCurvature u (S.levelSide u) (S.state u (S.levelSide u) w).1) ^ k)) w
          ∂(S.law u (S.levelSide u)) ≤ ENNReal.ofReal (C k * S.scaleCoupling ^ ((1 : ℝ) / 4000))) ∧
    ∀ (B : Finset (Fin Λ.k)) (N : ℕ),
      ∫⁻ w, Set.indicator {w | ¬ S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated)
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).2.1}
          (fun w => ENNReal.ofReal (∏ i ∈ B, |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)|)) w
          ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        ENNReal.ofReal (C N * S.scaleCoupling ^ (-(N : ℝ)))
end YangMills.Construction.MomentLaw
end
