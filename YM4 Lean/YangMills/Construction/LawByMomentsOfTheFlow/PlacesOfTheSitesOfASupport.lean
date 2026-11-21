import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
def supportSitesLocationStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (k : ℕ) (P : LevelData k) (t : ℕ), t ≤ P.windowLevel → ∀ i : Fin k,
    (∀ y ∈ P.supportSites L t i, ∃ z : TestFunctions.EuclideanFourSpace, P.fn i z ≠ 0 ∧ ∀ a : Fin 4,
      |circleRep (P.period L) (((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ P.windowLevel - P.center a -
        (L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * z a)| ≤ (L : ℝ) ^ t / (2 * (L : ℝ) ^ P.windowLevel)) ∧
    ((∃ p : WeightedResponses.OrientedPlaquette (P.period L * L ^ P.windowLevel), P.testWeight L i _ p.1 ≠ 0) →
      (P.supportSites L t i).Nonempty)
end YangMills.Construction.LevelTestFunctions
end
