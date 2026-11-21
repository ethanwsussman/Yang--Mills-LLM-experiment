import YangMills.Construction.LawThroughTheLevels.LevelsOverFourSpace
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Scales
def SeparatedPairsAreTestFunctionsStatement : Prop :=
  ∀ (d ϑ : ℝ) (f h : (Fin 4 → ℝ) → ℝ), 0 ≤ d → (f, h) ∈ TestFunctions.separatedPairsR4 d ϑ →
    f ∈ lipschitzCompactR4 ∧ h ∈ lipschitzCompactR4
end YangMills.Construction.Scales
end
