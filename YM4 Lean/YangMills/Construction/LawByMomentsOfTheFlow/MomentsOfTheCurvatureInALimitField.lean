import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.WindowClearOfHulls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
def curvatureLimitMomentStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (X₀ : ℝ), Λ.floor ≤ X₀ ∧
    ∀ (S : MomentPoint Λ) (L : LimitLawAtPoint S) (t : ℕ), X₀ ≤ S.scaleCoupling →
    (∀ i, (L.points i).lastSeparated = t) → ∀ (u : ℕ), t ≤ u → u ≤ t + S.logIndex + 2 →
      ∀ (z : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ a, (z a).natAbs ≤ 4 * S.range ^ 2) → ∀ (q : ℕ) (j : L.Index), 1 ≤ q →
        L.observables j = clearCurvaturePower u z μ ν q →
        ∀ᵐ ω ∂L.law, L.condMeanAt j ω ≤ C q * S.scaleCoupling ^ (-(q : ℝ))
end YangMills.Construction.MomentLaw
end
