import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseMaps
open CriticalBranchResponse
structure OnTower (L n k : ℕ) : Prop where
  coboundary_eq : ∀ B : edgeFormSpace L n k 0,
    (formCoboundary L n k B : Face L n k 0 → Matrices.ComplexMatrix2) =
      edgeCoboundary (B : Edge L n k 0 → Matrices.ComplexMatrix2)
  crossing_eq : ∀ B : edgeFormSpace L n k 0,
    (crossingSmoothingToTop L n k B : Edge L n k k → Matrices.ComplexMatrix2) =
      crossingSmoothingIter L n k k B
  linear_eq : ∀ B : edgeFormSpace L n k 0,
    (linearSmoothingToTop L n k B : Edge L n k k → Matrices.ComplexMatrix2) =
      linearSmoothingIter L n k k B
  coboundary_transpose : ∀ (g : faceFunctionSpace L n k 0) (f : edgeFormSpace L n k 0),
    edgeFormPairing (formCoboundaryTranspose L n k g : Edge L n k 0 → Matrices.ComplexMatrix2) f =
      traceFinsumPairing (g : Face L n k 0 → Matrices.ComplexMatrix2)
        (formCoboundary L n k f : Face L n k 0 → Matrices.ComplexMatrix2)
  crossing_transpose : ∀ (g : edgeFormSpace L n k k) (f : edgeFormSpace L n k 0),
    edgeFormPairing (crossingSmoothingTranspose L n k g : Edge L n k 0 → Matrices.ComplexMatrix2) f =
      edgeFormPairing (g : Edge L n k k → Matrices.ComplexMatrix2)
        (crossingSmoothingToTop L n k f : Edge L n k k → Matrices.ComplexMatrix2)
  linear_transpose : ∀ (g : edgeFormSpace L n k k) (f : edgeFormSpace L n k 0),
    edgeFormPairing (linearSmoothingTranspose L n k g : Edge L n k 0 → Matrices.ComplexMatrix2) f =
      edgeFormPairing (g : Edge L n k k → Matrices.ComplexMatrix2)
        (linearSmoothingToTop L n k f : Edge L n k k → Matrices.ComplexMatrix2)
  linear_surjective : Function.Surjective (linearSmoothingToTop L n k)
  face_pairing_definite : ∀ g : faceFunctionSpace L n k 0,
    traceFinsumPairing (g : Face L n k 0 → Matrices.ComplexMatrix2)
      (g : Face L n k 0 → Matrices.ComplexMatrix2) = 0 → g = 0
def ResponseMapsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n → OnTower L n k
end YangMills.Construction.Tower.ResponseMaps
end
