import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
section StepExpansion
variable {L n k i : ℕ}
def stepLog (V : Edge L n k i → Matrices.ComplexMatrix2) (c : PositiveEdge L n k (i + 1))
    (B : Edge L n k i → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
    (smoothingStep L n k i (PeriodicLattice.expTwist B V) c * (smoothingStep L n k i V c)⁻¹)
def taylorCoeffAtZero (r : ℕ) (f : (Edge L n k i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2)
    (B : Edge L n k i → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  ((r.factorial : ℝ)⁻¹) • iteratedDeriv r (fun t : ℝ => f ((t : ℂ) • B)) 0
def IsAnalyticNearZero (f : (Edge L n k i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) :
    Prop :=
  ∃ _ : Fintype (PositiveEdge L n k i), ∃ W : Set (Empty ⊕ PositiveEdge L n k i → Matrices.ComplexMatrix2),
    Matrices.GroupLieProduct.Subspaces.ofParts Empty.elim 0 ∈ W ∧
    Matrices.GroupLieProduct.Subspaces.IsSubspaceAnalyticToCoords (R := Empty)
      (S := PositiveEdge L n k i) (l := 4)
      (Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k i)) W
      fun q => Coordinates.ComplexCoordinates.matrixEquiv
        (f (edgeFormOfPositiveValues (Matrices.GroupLieProduct.Subspaces.algebraComponent q)))
abbrev EdgeFormBilinear (L n k i : ℕ) : Type :=
  edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k i →ₗ[ℝ]
    PositiveEdge L n k (i + 1) → Matrices.ComplexMatrix2
def IsQuadraticExpansion (V : Edge L n k i → Matrices.ComplexMatrix2) (q : EdgeFormBilinear L n k i) :
    Prop :=
  (∀ B B' : edgeFormSpace L n k i, q B B' = q B' B) ∧
    ∀ c : PositiveEdge L n k (i + 1), ∃ C : ℝ, ∀ᶠ B : edgeFormSpace L n k i in 𝓝 0,
      Matrices.ComplexMatrix2.operatorNorm (stepLog V c B - leftDifferential (smoothingStep L n k i) V B c -
        (1 / 2 : ℝ) • q B B c) ≤ C * edgeFormNorm (B : Edge L n k i → Matrices.ComplexMatrix2) ^ 3
def StepLogAnalytic (V : Edge L n k i → Matrices.ComplexMatrix2) : Prop :=
  (∀ᶠ B : edgeFormSpace L n k i in 𝓝 0, ∀ c : PositiveEdge L n k (i + 1),
    smoothingStep L n k i (PeriodicLattice.expTwist (B : Edge L n k i → Matrices.ComplexMatrix2) V) c ∈
        PeriodicLattice.compactGaugeGroup ∧
      smoothingStep L n k i V c ∈ PeriodicLattice.compactGaugeGroup ∧
      smoothingStep L n k i (PeriodicLattice.expTwist (B : Edge L n k i → Matrices.ComplexMatrix2) V) c *
        (smoothingStep L n k i V c)⁻¹ ∈ Matrices.ComplexMatrix2.logBall ∧
      stepLog V c B ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
    ∀ c : PositiveEdge L n k (i + 1),
      IsAnalyticNearZero (stepLog V c) ∧ stepLog V c 0 = 0
def StepDifferentialIsLinearTerm (V : Edge L n k i → Matrices.ComplexMatrix2) : Prop :=
  (∃ D : Set (Edge L n k i → Matrices.ComplexMatrix2), V ∈ D ∧
      IsDifferentiableFieldMap D (smoothingStep L n k i)) ∧
    (∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1), ∀ B : edgeFormSpace L n k i,
      (T B : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = leftDifferential (smoothingStep L n k i) V B) ∧
    ∀ (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)),
      taylorCoeffAtZero 1 (stepLog V c) B =
          deriv (fun t : ℝ => stepLog V c ((t : ℂ) • (B : Edge L n k i → Matrices.ComplexMatrix2))) 0 ∧
        deriv (fun t : ℝ => stepLog V c ((t : ℂ) • (B : Edge L n k i → Matrices.ComplexMatrix2))) 0 =
          leftDifferential (smoothingStep L n k i) V B c
def StepHasQuadraticExpansion (V : Edge L n k i → Matrices.ComplexMatrix2) : Prop :=
  (∃! q : EdgeFormBilinear L n k i, IsQuadraticExpansion V q) ∧
    ∀ q : EdgeFormBilinear L n k i, IsQuadraticExpansion V q →
      (∀ (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)),
        (1 / 2 : ℝ) • q B B c = taylorCoeffAtZero 2 (stepLog V c) B) ∧
      (∀ (B B' : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)),
        q B B' c ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
      ∀ B B' : edgeFormSpace L n k i, edgeFormOfPositiveValues (q B B') ∈ edgeFormSpace L n k (i + 1)
end StepExpansion
def LeftChartStepExpansion : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k i) fun V =>
      StepLogAnalytic V ∧ StepDifferentialIsLinearTerm V ∧ StepHasQuadraticExpansion V
end Tower
end YangMills.Construction
end
