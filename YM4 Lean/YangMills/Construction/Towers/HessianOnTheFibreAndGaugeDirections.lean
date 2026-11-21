import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import YangMills.Construction.Towers.TermOfTheSecondOrderAndCommutatorTerm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k : ℕ}
def LeftSecondDerivGaugeIdentity (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ B ∈ edgeFormSpace L n k 0, ∀ l ∈ vertexFunctionSpace L n k 0,
    ((leftSecondDeriv (plaquetteAction L n k) U B (covDiff U l) : ℝ) : ℂ) =
      edgeFormPairing (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U)
        (bracketTerm U l B)
def IsInCovariantIterKernel (W : Edge L n k k → Matrices.ComplexMatrix2)
    (B : edgeFormSpace L n k 0) : Prop :=
  complexIterDeriv L n k k (chainBottom W) B = 0
def FibreHessianFormula (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  ∀ B : edgeFormSpace L n k 0, IsInCovariantIterKernel W B →
    ∃ hB : B ∈ LinearMap.ker (topConstraintMap L n k W),
      ((fibreRestrictedHessian L n k W ⟨B, hB⟩ : ℝ) : ℂ) =
        ((leftSecondDeriv (plaquetteAction L n k) (chainBottom W)
            (B : Edge L n k 0 → Matrices.ComplexMatrix2) B : ℝ) : ℂ) -
          traceFinsumPairing
            (restrictToPositiveEdges ((chosenCriticalBranch L n k).energyGradient k W))
            (iterQuadraticTerm (chainBottom W) B B)
def IsGaugeDirectionEmbedding (W : Edge L n k k → Matrices.ComplexMatrix2)
    (D : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] edgeFormSpace L n k 0) : Prop :=
  ∀ κ : vertexFunctionsVanishingAtTop L n k,
    (D κ : Edge L n k 0 → Matrices.ComplexMatrix2) = covDiff (chainBottom W) κ
def IsContourOfGaugeDirections (W : Edge L n k k → Matrices.ComplexMatrix2)
    (D : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] edgeFormSpace L n k 0)
    (T : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] vertexFunctionsVanishingAtTop L n k) : Prop :=
  ∀ κ : vertexFunctionsVanishingAtTop L n k,
    fineOnlyComponents (T κ : Vertex L n k 0 → Matrices.ComplexMatrix2) = contourFamily W (D κ)
def FibreGaugeDirections (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  ∃ D : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] edgeFormSpace L n k 0,
    IsGaugeDirectionEmbedding W D ∧
    (∃ hD : ∀ κ, D κ ∈ LinearMap.ker (topConstraintMap L n k W),
      ∀ (κ : vertexFunctionsVanishingAtTop L n k) (B : edgeFormSpace L n k 0),
        IsInCovariantIterKernel W B →
        ∃ hB : B ∈ LinearMap.ker (topConstraintMap L n k W),
          fibreRestrictedHessian L n k W (⟨B, hB⟩ + ⟨D κ, hD κ⟩) =
            fibreRestrictedHessian L n k W ⟨B, hB⟩) ∧
    (∀ (κ : vertexFunctionsVanishingAtTop L n k) (i : Fin k) (y : Vertex L n k ((i : ℕ) + 1))
        (x : FineOnlyVertex L n k i),
      x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      (x.1 : PeriodicLattice.FourTorus L n) ≠ y →
      contourFamily W (D κ) i x =
        restrictVertexFunction (i : ℕ) (κ : Vertex L n k 0 → Matrices.ComplexMatrix2) x.1 -
          restrictVertexFunction ((i : ℕ) + 1) (κ : Vertex L n k 0 → Matrices.ComplexMatrix2) y) ∧
    ∃ T : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] vertexFunctionsVanishingAtTop L n k,
      IsContourOfGaugeDirections W D T ∧ |LinearMap.det T| = 1
def FibreHessianAndGaugeDirections : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k 0) LeftSecondDerivGaugeIdentity ∧
      EventuallyNearIdentity (fieldSpace L n k k) fun W =>
        FibreHessianFormula W ∧ FibreGaugeDirections W
end YangMills.Construction.Tower
end
