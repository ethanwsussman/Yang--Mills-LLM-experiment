import YangMills.Construction.Towers.DifferentialsOfRealAnalyticMaps
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheResponseOperators
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace CriticalBranchResponse
open PeriodicOperators (colourEdges applyKernel periodicMatrix)
open BackgroundFieldResponse (responseKernel responseDefect)
open ResponseOperators (ClassFnEqForm)
open LocalKernels.Periodisation (periodSide)
open AnalyticDifferentials (HasFormDerivAtZero)
open Matrices (ComplexMatrix2)
def IsPeriodicImage (L n k i j : ℕ)
    (T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ)
    (A : Edge L n k i → ComplexMatrix2) (A' : edgeFormSpace L n k j) : Prop :=
  ∃ g, ClassFnEqForm L n k i (restrictToPositiveEdges A) g ∧
    ClassFnEqForm L n k j (restrictToPositiveEdges (A' : Edge L n k j → ComplexMatrix2))
      (applyKernel (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n)) g)
def periodicImage (L n k i j : ℕ)
    (T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ)
    (A : Edge L n k i → ComplexMatrix2) : edgeFormSpace L n k j :=
  Classical.epsilon (IsPeriodicImage L n k i j T A)
def periodicResponse (L n k : ℕ) (A : Edge L n k k → ComplexMatrix2) : edgeFormSpace L n k 0 :=
  periodicImage L n k k 0 (responseKernel L k) A
def periodicDefect (L n k : ℕ) (A : Edge L n k k → ComplexMatrix2) : edgeFormSpace L n k k :=
  periodicImage L n k k k (responseDefect L k) A
def meshScaledResponse (L n k : ℕ) (A : Edge L n k k → ComplexMatrix2) : edgeFormSpace L n k 0 :=
  finestMesh L k • periodicResponse L n k A
def formCoboundary (L n k : ℕ) : edgeFormSpace L n k 0 →ₗ[ℝ] faceFunctionSpace L n k 0 :=
  linearMapWithValues _ _ edgeCoboundary
def formCoboundaryTranspose (L n k : ℕ) : faceFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0)
    (S' := pairedFunctions (Face L n k 0)) (formCoboundary L n k)
def crossingSmoothingToTop (L n k : ℕ) : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k :=
  linearMapWithValues _ _ (crossingSmoothingIter L n k k)
def crossingSmoothingTranspose (L n k : ℕ) : edgeFormSpace L n k k →ₗ[ℝ] edgeFormSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0) (S' := edgePairedSpace L n k k)
    (crossingSmoothingToTop L n k)
def linearSmoothingToTop (L n k : ℕ) : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k :=
  linearMapWithValues _ _ (linearSmoothingIter L n k k)
def linearSmoothingTranspose (L n k : ℕ) : edgeFormSpace L n k k →ₗ[ℝ] edgeFormSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0) (S' := edgePairedSpace L n k k)
    (linearSmoothingToTop L n k)
def expLineField (L n k : ℕ) (A : Edge L n k k → ComplexMatrix2) (t : ℝ) : Edge L n k k → ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • A) (trivialField L n k k)
def GradientExistsAt {L n k j : ℕ} (F : (Edge L n k j → ComplexMatrix2) → ℝ)
    (U : Edge L n k j → ComplexMatrix2) : Prop :=
  (∃ D : Set (Edge L n k j → ComplexMatrix2), U ∈ D ∧ IsDifferentiableFn D F) ∧
    IsLeftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U
      (leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U)
def IsFormCurveDerivAtZero {L n k j : ℕ} (X : ℝ → Edge L n k j → ComplexMatrix2)
    (Y : edgeFormSpace L n k j) : Prop :=
  ∃ γ : ℝ → edgeFormSpace L n k j, (∀ᶠ t in 𝓝 (0 : ℝ), (γ t : Edge L n k j → ComplexMatrix2) = X t) ∧
    HasFormDerivAtZero γ Y
end CriticalBranchResponse
end Tower
end YangMills.Construction
end
