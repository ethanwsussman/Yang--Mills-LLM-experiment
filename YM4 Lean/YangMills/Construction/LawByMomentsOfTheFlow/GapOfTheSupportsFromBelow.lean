import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
def separationLowerBoundStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → 3 ≤ L → ∀ k : ℕ, 2 ≤ k → ∀ R d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
    ∀ P : LevelData k, P.Admissible L R d → ∀ u < P.windowLevel,
      c * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) - 12 ≤ (P.separation L u : ℝ)
end YangMills.Construction.LevelTestFunctions
end
