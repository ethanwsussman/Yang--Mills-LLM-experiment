import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowClearOfHulls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
def hullsClearLimitStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C c X₀ : ℝ, 0 < c ∧ Λ.floor ≤ X₀ ∧
    ∀ (S : MomentPoint Λ) (L : LimitLawAtPoint S) (t : ℕ), X₀ ≤ S.scaleCoupling →
    (∀ i, (L.points i).lastSeparated = t) → ∀ (u : ℕ) (j : L.Index), t ≤ u → L.observables j = notClearIndicator u →
      ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C * Real.exp (-(c * S.scaleCoupling))
end YangMills.Construction.MomentLaw
end
