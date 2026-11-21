import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TorusResponseRelations
open CriticalBranchResponse
open BackgroundFieldResponse (responseKernel responseDefect)
structure HoldsAt (L n k : ℕ) (B : edgeFormSpace L n k k) : Prop where
  image_response : IsPeriodicImage L n k k 0 (responseKernel L k) B (periodicResponse L n k B)
  image_defect : IsPeriodicImage L n k k k (responseDefect L k) B (periodicDefect L n k B)
  smoothing_eq : crossingSmoothingIter L n k k (meshScaledResponse L n k B) = B
  coboundary_eq : formCoboundaryTranspose L n k (formCoboundary L n k (meshScaledResponse L n k B)) =
    crossingSmoothingTranspose L n k (periodicDefect L n k B)
  pairing_vertex_eq_zero : ∀ l ∈ vertexFunctionSpace L n k k,
    edgeFormPairing (periodicDefect L n k B : Edge L n k k → Matrices.ComplexMatrix2) (vertexCoboundary l) = 0
def statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ B : edgeFormSpace L n k k, HoldsAt L n k B
end YangMills.Construction.Tower.TorusResponseRelations
end
