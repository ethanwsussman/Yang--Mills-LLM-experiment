import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses TorusFields
def gaussianChainMomentsStatement : Prop :=
  ForAllHullPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
    ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
    IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
    ∀ B : Finset (Fin Λ.k),
    |S.scaleCoupling ^ B.card * ∫ w, ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) -
      ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
      C 0 * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) ∧
    |S.scaleCoupling ^ B.card * ∫ w, ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))| ≤
      C 1 * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000) ∧
    |∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
      C 1 * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)
end YangMills.Construction.MomentLaw
end
