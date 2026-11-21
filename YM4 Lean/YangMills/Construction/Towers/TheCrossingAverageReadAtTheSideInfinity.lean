import YangMills.Construction.Towers.PeriodicExtensionOfTheFormsOfATower
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CrossingSmoothingAtInfinity
open YangMills.Construction.PeriodicOperators (RowFinite applyKernel)
open YangMills.Construction.Tower.PeriodicForm (coeffsOnEdges)
open YangMills.Construction.Tower.CriticalBranchResponse
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
structure CrossingSmoothingAtSide (L n k : ℕ) : Prop where
  Q_rowFinite : RowFinite (trivialRescaledOperators L k).Q
  Qt_rowFinite : RowFinite (trivialRescaledOperators L k).Qt
  coe_eq_iter : ∀ A : edgeFormSpace L n k 0,
    (crossingSmoothingToTop L n k A : Edge L n k k → Matrices.ComplexMatrix2) =
      crossingSmoothingIter L n k k A
  coeffs_smoothing : ∀ A : edgeFormSpace L n k 0,
    (finestMesh L k : ℂ) • coeffsOnEdges L n k k (crossingSmoothingToTop L n k A) =
      applyKernel (trivialRescaledOperators L k).Q (coeffsOnEdges L n k 0 A)
  coeffs_transpose : ∀ μ : edgeFormSpace L n k k,
    coeffsOnEdges L n k 0 (crossingSmoothingTranspose L n k μ) =
      ((finestMesh L k : ℂ) ^ 3) • applyKernel (trivialRescaledOperators L k).Qt (coeffsOnEdges L n k k μ)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    CrossingSmoothingAtSide L n k
end YangMills.Construction.Tower.CrossingSmoothingAtInfinity
end
