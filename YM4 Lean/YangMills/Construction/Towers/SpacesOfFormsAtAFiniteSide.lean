import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FiniteSideFormSpaces : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    Finite (PositiveEdge L n k j) ∧
    FiniteDimensional ℝ (edgeFormSpace L n k j) ∧
    Module.finrank ℝ (edgeFormSpace L n k j) = 3 * Nat.card (PositiveEdge L n k j) ∧
    ∃ c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j),
      ∀ B B' : edgeFormSpace L n k j,
        edgeFormPairing (B : Edge L n k j → Matrices.ComplexMatrix2)
            (B' : Edge L n k j → Matrices.ComplexMatrix2) =
          ((c.inner B B' : ℝ) : ℂ)
end YangMills.Construction.Tower
end
