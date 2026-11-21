import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def limitResponseMomentStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C X₀ : ℝ, Λ.floor ≤ X₀ ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (d : ℕ → ℕ)
    (μ : ∀ m, Measure (LevelChain Λ.stepParams.side ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side))),
    (∀ m, (F.points m).lastSeparated + d m = (F.points m).data.windowLevel) →
    (∀ m, IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling ((F.points m).lastSeparated + d m)
      ((F.points m).data.period Λ.stepParams.side)) (μ m)) →
    ∀ (B : Finset (Fin Λ.k)) (e : ℝ),
      Tendsto (fun m => ∫ X, ∏ i ∈ B, (F.points m).halfForm (d m) ((F.points m).data.period Λ.stepParams.side) i X ∂(μ m))
        atTop (𝓝 e) →
      ∀ j : F.Index, F.observables j = responseProduct B → X₀ ≤ S.scaleCoupling →
        ∀ᵐ v ∂F.law, |S.scaleCoupling ^ B.card * F.condMeanAt j v - e| ≤
          C * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ)
end YangMills.Construction.MomentLaw
end
