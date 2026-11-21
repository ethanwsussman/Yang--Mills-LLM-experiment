import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowInALimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
def meanScoreLimitMomentStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C : ℝ, ∀ (S : MomentPoint Λ) (L : LimitLawAtPoint S) (p : ℕ), 1 ≤ p →
    ∀ (J : List (Fin Λ.k)) (j : L.Index), J.length = p → L.observables j = meanScoreProduct J →
      ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C ^ p * (p.factorial : ℝ) ^ 6
end YangMills.Construction.MomentLaw
end
