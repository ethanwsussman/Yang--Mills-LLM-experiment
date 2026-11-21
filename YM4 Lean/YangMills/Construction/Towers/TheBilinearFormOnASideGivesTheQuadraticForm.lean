import YangMills.Construction.Towers.TheFactorsOfTheBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.BilinearOnDiagonal
def DiagonalIsHessianForm : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
      ∀ (J : Tower.edgeFormSpace L n k 0) (μ : Tower.edgeFormSpace L n k k)
        (B : Tower.edgeFormSpace L n k 0),
        Tower.backgroundBilinear U (J : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
            (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2)
            (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
            (B : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) =
          (Tower.backgroundHessianForm U J μ B : ℂ)
end YangMills.Construction.Tower.BilinearOnDiagonal
end
