import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def lastSeparatedLevelMomentStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (X₀ : ℝ), Λ.floor ≤ X₀ ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ),
    (∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i))) → ∀ (B : Finset (Fin Λ.k)) (j j' : F.Index),
      F.observables j = bottomProduct c B → F.observables j' = responseProduct B →
      (X₀ ≤ S.scaleCoupling → ∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))) ∧
      ∀ M : ℕ, S.scaleCoupling ≤ M → ∀ᵐ v ∂F.law, |F.condMeanAt j v| ≤ C M
end YangMills.Construction.MomentLaw
end
