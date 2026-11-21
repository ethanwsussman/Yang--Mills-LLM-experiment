import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
def separationUpperBoundStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → 3 ≤ L → ∀ k : ℕ, 2 ≤ k → ∀ R d : ℝ, 0 < d → ∃ C : ℝ, 0 ≤ C ∧
    ∀ P : LevelData k, P.Admissible L R d → ∀ u < P.windowLevel,
      (P.separation L u : ℝ) ≤ C * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) + 2
end YangMills.Construction.LevelTestFunctions
end
