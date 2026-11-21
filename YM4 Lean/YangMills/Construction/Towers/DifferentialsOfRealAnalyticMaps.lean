import YangMills.Construction.Towers.RealAnalyticMapsNearAConfiguration
import YangMills.Construction.Towers.TwoStagesOfAConstraintDefs
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AnalyticDifferentials
open AnalyticNearField
variable {L n k j j' : ℕ}
def IsSmoothFn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → E) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup D ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    Manifolds.IsSmoothOnOpen (Matrices.specialUnitaryPower (PositiveEdge L n k j))
      (restrictToPositiveEdges '' D) fun w => F (fieldOfPositiveValues w)
def IsSmoothFieldMap (D : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (f : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2) :
    Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup D ∧ MapsTo f D (fieldSpace L n k j') ∧
    ∃ (_ : Fintype (PositiveEdge L n k j)) (_ : Fintype (PositiveEdge L n k j')),
      Manifolds.IsSmoothOnOpen (Matrices.specialUnitaryPower (PositiveEdge L n k j))
        (restrictToPositiveEdges '' D) fun w => restrictToPositiveEdges (f (fieldOfPositiveValues w))
def HasLeftGradientAt (D : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℂ)
    (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  (∀ B ∈ edgeFormSpace L n k j,
    DifferentiableAt ℝ (fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) V)) 0) ∧
  IsLeftGradient D F V (leftGradient D F V) ∧ ∀ X, IsLeftGradient D F V X → X = leftGradient D F V
def HasLeftSecondDerivAt (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℂ)
    (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
    (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ
      (fun t : ℝ => F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') V)) 0) ∧
    DifferentiableAt ℝ
      (fun s : ℝ => deriv
        (fun t : ℝ => F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') V)) 0) 0
def HasLeftDifferentialAt
    (f : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ B ∈ edgeFormSpace L n k j, ∀ c : Edge L n k j', c.IsPositivelyOriented →
    (∀ᶠ t : ℝ in 𝓝 0,
      Matrices.ComplexMatrix2.operatorNorm
        (f (PeriodicLattice.expTwist ((t : ℂ) • B) V) c * (f V c)⁻¹ - 1) < 1) ∧
    DifferentiableAt ℝ
      (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
        (f (PeriodicLattice.expTwist ((t : ℂ) • B) V) c * (f V c)⁻¹)) 0
def LeftDifferentialIsLinear
    (f : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (V : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ B : edgeFormSpace L n k j,
    (leftDifferentialLinear f V B : Edge L n k j' → Matrices.ComplexMatrix2) = leftDifferential f V B
def leftDifferentialTranspose
    (f : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (V : Edge L n k j → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k j' →ₗ[ℝ] edgeFormSpace L n k j :=
  PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k j) (S' := edgePairedSpace L n k j')
    (leftDifferentialLinear f V)
def colorCoords (B : Edge L n k j → Matrices.ComplexMatrix2) : PositiveEdge L n k j × Fin 3 → ℝ :=
  Classical.epsilon fun x => formOfCoeffs x = B
def IsContinuousCurveStartingIn (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) (I : Set ℝ)
    (γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  IsOpenIntervalAroundZero I ∧ MapsTo γ I (fieldSpace L n k j) ∧ γ 0 ∈ W ∧
    ∀ b : Edge L n k j, b.IsPositivelyOriented → ∀ r s : Fin 2, ContinuousOn (fun t => γ t b r s) I
def HasFormDerivAtZero (χ : ℝ → edgeFormSpace L n k j) (d : edgeFormSpace L n k j) : Prop :=
  ∀ b : Edge L n k j,
    HasDerivAt (fun t => (χ t : Edge L n k j → Matrices.ComplexMatrix2) b)
      ((d : Edge L n k j → Matrices.ComplexMatrix2) b) 0
def AnalyticFnsSmooth (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  ∀ F : (Edge L n k j → Matrices.ComplexMatrix2) → ℂ, IsAnalyticComplexFieldFunction W F →
    IsSmoothFn W F ∧ IsDifferentiableFn W F ∧
      IsTwiceDifferentiableFn W F ∧
      ∀ V ∈ W, HasLeftGradientAt W F V ∧ HasLeftSecondDerivAt F V
def AnalyticMapsSmooth (j' : ℕ) (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  ∀ F : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2,
    IsAnalyticFieldMap W F →
    IsSmoothFieldMap W F ∧ IsDifferentiableFieldMap W F ∧
      ∀ V ∈ W, HasLeftDifferentialAt F V ∧ LeftDifferentialIsLinear F V
def DifferentialContinuousAlongCurves (j' : ℕ) (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) :
    Prop :=
  ∀ (p : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (I : Set ℝ) (γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2),
    IsAnalyticFieldMap W p → IsContinuousCurveStartingIn W I γ →
    (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W) ∧
    ∀ B ∈ edgeFormSpace L n k j, ∃ J ∈ 𝓝 (0 : ℝ), ∀ i : PositiveEdge L n k j' × Fin 3,
      ContinuousOn (fun t => colorCoords (leftDifferential p (γ t) B) i) J
def TransposeDifferentiableAlongCurves (j' : ℕ) (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) :
    Prop :=
  ∀ (p : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (I : Set ℝ) (γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2)
    (χ : ℝ → edgeFormSpace L n k j') (χ' : edgeFormSpace L n k j'),
    IsAnalyticFieldMap W p → IsContinuousCurveStartingIn W I γ → χ 0 = 0 →
    HasFormDerivAtZero χ χ' →
    (∀ᶠ t in 𝓝 (0 : ℝ), LeftDifferentialIsLinear p (γ t) ∧ ∀ B : edgeFormSpace L n k j,
      edgeFormPairing
          (leftDifferentialTranspose p (γ t) (χ t) : Edge L n k j → Matrices.ComplexMatrix2)
          (B : Edge L n k j → Matrices.ComplexMatrix2) =
        edgeFormPairing (χ t : Edge L n k j' → Matrices.ComplexMatrix2)
          (leftDifferentialLinear p (γ t) B : Edge L n k j' → Matrices.ComplexMatrix2)) ∧
    HasFormDerivAtZero (fun t => leftDifferentialTranspose p (γ t) (χ t))
      (leftDifferentialTranspose p (γ 0) χ')
def AnalyticMapsDifferentiable : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    ∀ W : Set (Edge L n k j → Matrices.ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup W →
      AnalyticFnsSmooth W ∧ AnalyticMapsSmooth j' W ∧
        DifferentialContinuousAlongCurves j' W ∧ TransposeDifferentiableAlongCurves j' W
end AnalyticDifferentials
end Tower
end YangMills.Construction
end
