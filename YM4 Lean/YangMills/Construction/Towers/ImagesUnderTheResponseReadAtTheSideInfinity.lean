import YangMills.Construction.Towers.PeriodicExtensionOfTheFormsOfATower
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseImagesFullSide
structure AtForm (L m k : ℕ) (B : Tower.edgeFormSpace L m k k) : Prop where
  resp_isImage : Tower.CriticalBranchResponse.IsPeriodicImage L m k k 0
    (Tower.BackgroundFieldResponse.responseKernel L k) B
    (Tower.CriticalBranchResponse.periodicResponse L m k B)
  defect_isImage : Tower.CriticalBranchResponse.IsPeriodicImage L m k k k
    (Tower.BackgroundFieldResponse.responseDefect L k) B
    (Tower.CriticalBranchResponse.periodicDefect L m k B)
  resp_summable : ∀ j, PeriodicOperators.ApplySummableAt
    (Tower.BackgroundFieldResponse.responseKernel L k) (Tower.PeriodicForm.coeffsOnEdges L m k k B) j
  defect_summable : ∀ j, PeriodicOperators.ApplySummableAt
    (Tower.BackgroundFieldResponse.responseDefect L k) (Tower.PeriodicForm.coeffsOnEdges L m k k B) j
  resp_coeffs : Tower.PeriodicForm.coeffsOnEdges L m k 0
      (Tower.CriticalBranchResponse.periodicResponse L m k B) =
    PeriodicOperators.applyKernel (Tower.BackgroundFieldResponse.responseKernel L k)
      (Tower.PeriodicForm.coeffsOnEdges L m k k B)
  defect_coeffs : Tower.PeriodicForm.coeffsOnEdges L m k k
      (Tower.CriticalBranchResponse.periodicDefect L m k B) =
    PeriodicOperators.applyKernel (Tower.BackgroundFieldResponse.responseDefect L k)
      (Tower.PeriodicForm.coeffsOnEdges L m k k B)
def ResponseImagesHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 0 < m →
    ∀ B : Tower.edgeFormSpace L m k k, AtForm L m k B
end YangMills.Construction.Tower.ResponseImagesFullSide
end
