import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def cumulantByGaussianChainStatement : Prop :=
  ForAllHullPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
    ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
    IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
    |S.scaleCoupling ^ Λ.k * S.responseCumulant -
        jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i)| ≤
      C 0 * (S.range : ℝ) ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000) ∧
    |S.scaleCoupling ^ Λ.k * S.responseCumulant -
        jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i)| ≤
      C 1 * S.scaleCoupling ^ (-(1 / 10) : ℝ)
end YangMills.Construction.MomentLaw
end
