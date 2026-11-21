import YangMills.Construction.Towers.PeriodicExtensionOfTheFormsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PeriodicCoeffsDetermineForm
open PeriodicForm (coeffsOnEdges)
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n j : ℕ, 0 < n → j ≤ k →
    (∀ A A' : edgeFormSpace L n k j, coeffsOnEdges L n k j A = coeffsOnEdges L n k j A' → A = A') ∧
    ∀ (c : ℝ) (A : edgeFormSpace L n k j),
      coeffsOnEdges L n k j (c • A : edgeFormSpace L n k j) = (c : ℂ) • coeffsOnEdges L n k j A
end YangMills.Construction.Tower.PeriodicCoeffsDetermineForm
end
