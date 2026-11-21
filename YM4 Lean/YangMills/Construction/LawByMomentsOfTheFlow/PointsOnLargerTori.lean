import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def largerToriStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ S : MomentPoint Λ, (∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      ({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).SupAdmissible
        Λ.stepParams.side Λ.R Λ.d ∧
      Λ.stepParams.side * Λ.stepParams.n₀ ≤
        ({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).period Λ.stepParams.side) ∧
    (∃ b : ℝ, ∀ (m : ℕ) hp hs (i : Fin Λ.k), |(S.withSideExponent m hp hs).kappaAtLast i| ≤ b) ∧
    (∃ rule : ChainNoise.NoiseRule Λ.stepParams, rule.IsAdmissible S.tower) ∧
    ∀ (rule : ChainNoise.NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ),
      rule.IsAdmissible S.tower → 1 ≤ p → StrictMono ms →
      (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving ∧
      ∀ (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)),
        MomentMethod.TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (bottomProduct c B)) ∧
        MomentMethod.TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseProduct B))
end YangMills.Construction.MomentLaw
end
