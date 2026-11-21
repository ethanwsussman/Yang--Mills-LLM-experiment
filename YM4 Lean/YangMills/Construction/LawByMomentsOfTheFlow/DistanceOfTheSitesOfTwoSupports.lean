import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
def SupportSiteDistanceBounds : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (k : ℕ) (R d : ℝ), 0 < d → ∀ P : LevelData k, P.Admissible L R d →
    ∀ t : ℕ, t ≤ P.windowLevel →
    ∀ (i j : Fin k), ∀ w ∈ P.supportSites L t i, ∀ w' ∈ P.supportSites L t j,
      (TorusFields.supDist w w' : ℝ) ≤ 2 * R * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (t : ℤ)) + 1 ∧
      (i ≠ j → d / 2 * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (t : ℤ)) ≤ (TorusFields.supDist w w' : ℝ) + 1)
end YangMills.Construction.LevelTestFunctions
end
