import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open YangMills.Construction.TorusLumps
def separationLevelNearScaleStatement : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∀ k : ℕ, 2 ≤ k → ∀ R d : ℝ, 0 < d → ∃ C : ℝ,
    ∀ P : LevelData k, P.Admissible ℓ.side R d → ∀ β : ℝ,
      (P.separationLevel ℓ β : ℝ) ≤ (P.scaleLevel : ℝ) + C
end YangMills.Construction.LevelTestFunctions
end
