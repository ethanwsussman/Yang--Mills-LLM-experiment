import YangMills.Construction.Towers.PeriodicExtensionOfTheFormsOfATower
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FormCoboundariesAtInfinity
open PeriodicOperators (RowFinite applyKernel)
open PeriodicForm (coeffsOnEdges)
open CriticalBranchResponse
open PlaneWaveCalculus (vertexCoboundaryT)
open ResponseProperties (coboundaryLaplacian)
structure FormCoboundariesAtSide (L n k : ℕ) : Prop where
  laplacian_rowFinite : RowFinite (coboundaryLaplacian L k)
  divergence_rowFinite : RowFinite (vertexCoboundaryT L k k)
  evaluation_laplacian : ∀ A : edgeFormSpace L n k 0,
    coeffsOnEdges L n k 0 (formCoboundaryTranspose L n k (formCoboundary L n k A)) =
      ((finestMesh L k : ℂ) ^ 2) • applyKernel (coboundaryLaplacian L k) (coeffsOnEdges L n k 0 A)
  pairing_coboundary_eq_zero : ∀ μ : edgeFormSpace L n k k,
    applyKernel (vertexCoboundaryT L k k) (coeffsOnEdges L n k k μ) = 0 →
      ∀ l ∈ vertexFunctionSpace L n k k,
        edgeFormPairing (μ : Edge L n k k → Matrices.ComplexMatrix2) (vertexCoboundary l) = 0
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    FormCoboundariesAtSide L n k
end YangMills.Construction.Tower.FormCoboundariesAtInfinity
end
