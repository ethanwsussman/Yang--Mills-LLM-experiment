import YangMills.Construction.Towers.SeriesOfUnitaryOperatorsWithSummableMatrixCoefficients
import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import YangMills.Construction.Towers.TransportsAroundAPlaquette
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace Tower
open UnitLatticeL2 AbelianFieldDensity
namespace AbelianFieldFacts
open PeriodicOperators (PeriodicData KernelMatrix shiftEdge colourVertices colourEdges)
open UnitaryCombinations (ScalarL2)
open Matrices
section Trigonometric
variable {E : Type}
def fourierMode (n : E → ℤ) (φ : E → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ᶠ β, (n β : ℝ) * φ β : ℝ) : ℂ))
def HasFourierCoeffs (Q : (E → ℝ) → ℂ) (γ : (E → ℤ) → ℂ) : Prop :=
  (Function.support γ).Finite ∧ ∀ φ, Q φ = ∑ᶠ n, γ n * fourierMode n φ
def IsTrigPolynomial (Q : (E → ℝ) → ℂ) : Prop :=
  Finite E ∧ Nonempty E ∧ ∃ γ, HasFourierCoeffs Q γ
end Trigonometric
def FourierCoeffsUnique : Prop :=
  ∀ (E : Type), Finite E → Nonempty E → ∀ (Q : (E → ℝ) → ℂ) (γ γ' : (E → ℤ) → ℂ),
    HasFourierCoeffs Q γ → HasFourierCoeffs Q γ' → γ = γ'
def cartanPhase (ϑ : ℝ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • ((ϑ : ℂ) • ComplexMatrix2.pauliFamily 2))
def ChargeAlgebra : Prop :=
  (∀ ϑ : ℝ, ComplexMatrix2.conjugateBy (cartanPhase ϑ) raisingPauli =
      Complex.exp (2 * Complex.I * (ϑ : ℂ)) • raisingPauli ∧
    ComplexMatrix2.conjugateBy (cartanPhase ϑ) loweringPauli =
      Complex.exp (-(2 * Complex.I * (ϑ : ℂ))) • loweringPauli) ∧
  ⁅raisingPauli, loweringPauli⁆ = ComplexMatrix2.pauliFamily 2 ∧
  ComplexMatrix2.halfTrace (raisingPauli * loweringPauli) = 1 / 2 ∧
  ComplexMatrix2.halfTrace (raisingPauli * raisingPauli) = 0 ∧
  ComplexMatrix2.halfTrace (loweringPauli * loweringPauli) = 0 ∧
  ComplexMatrix2.halfTrace (raisingPauli * ComplexMatrix2.pauliFamily 2) = 0 ∧
  ComplexMatrix2.halfTrace (loweringPauli * ComplexMatrix2.pauliFamily 2) = 0
def FormsChargeDecomposition (a : ℝ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace a, ∀ b : FullSpace.PositiveEdge a,
    B b.1 = ((FullSpace.diagonalComponent B b : ℝ) : ℂ) • ComplexMatrix2.pauliFamily 2 +
        FullSpace.offDiagonalComponent B b • raisingPauli +
        conj (FullSpace.offDiagonalComponent B b) • loweringPauli ∧
      ComplexMatrix2.operatorNorm (B b.1) ^ 2 =
        FullSpace.diagonalComponent B b ^ 2 + ‖FullSpace.offDiagonalComponent B b‖ ^ 2
variable {L : ℕ}
section Kernels
def abelianLaplacianKernel (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    KernelMatrix (VertexIndex L) (VertexIndex L) :=
  PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (FullSpace.Vertex L 0 0))
    (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.abelianGaugeLaplacian θ)
def abelianHessianKernel (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    KernelMatrix (EdgeIndex L) (EdgeIndex L) :=
  PauliComponentsOfSymmetricKernel.kernel (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
    (FullSpace.abelianMassiveHessian θ)
def edgesNear (L : ℕ) (y : InfiniteLattice.AmbientSpace) :
    Set (PeriodicOperators.PosEdge L 0 0) :=
  {b | TorusMetric.euclidNormVec ((b.1.initial : InfiniteLattice.AmbientSpace) - y) ≤ 2}
def HasRangeLeTwo {J : Type} (position : J → InfiniteLattice.AmbientSpace) (T : J → J → ℂ) :
    Prop :=
  ∀ ι' ι, ¬ TorusMetric.euclidNormVec (position ι' - position ι) ≤ 2 → T ι' ι = 0
def KernelEntriesTrigPoly (L : ℕ) (I : PeriodicData)
    (T : (FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ ι' ι, ∃ P : (edgesNear L (I.pos ι') → ℝ) → ℂ,
    IsTrigPolynomial P ∧
      ∀ (θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (ζ : Fin 4 → ℤ),
        T θ' (I.translate ζ ι') (I.translate ζ ι) = P fun b => θ' (shiftEdge ζ b.1)
structure KernelLocality (L : ℕ) : Prop where
  forwardEdge_mem : ∀ x : FullSpace.Vertex L 0 0,
    FullSpace.forwardEdge x 0 ∈ edgesNear L (x : InfiniteLattice.AmbientSpace)
  laplacian : KernelEntriesTrigPoly L (colourVertices L 0 0) abelianLaplacianKernel
  hessian : KernelEntriesTrigPoly L (colourEdges L 0 0) abelianHessianKernel
structure AbelianOperators (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop where
  laplacian_range : HasRangeLeTwo (vertexPos L) (abelianLaplacianKernel θ)
  hessian_range : HasRangeLeTwo (edgePos L) (abelianHessianKernel θ)
  laplacian_apply : ∀ v : L2Field (FullSpace.Vertex L 0 0),
    ofCoords (laplacianOp θ v) = FullSpace.abelianGaugeLaplacian θ (ofCoords v)
  hessian_apply : ∀ v : L2Field (PeriodicOperators.PosEdge L 0 0),
    ofCoords (AbelianFieldDensity.massiveOp θ v) =
      fun b => FullSpace.abelianMassiveHessian θ (formOfPositiveValues (ofCoords v)) b.1
  laplacian_isSelfAdjoint : IsSelfAdjointOp (laplacianOp θ)
  hessian_isSelfAdjoint : IsSelfAdjointOp (AbelianFieldDensity.massiveOp θ)
  laplacian_im : ∀ ι' ι, (abelianLaplacianKernel θ ι' ι).im = 0
  hessian_im : ∀ ι' ι, (abelianHessianKernel θ ι' ι).im = 0
  laplacian_symm : ∀ ι' ι, abelianLaplacianKernel θ ι' ι = abelianLaplacianKernel θ ι ι'
  hessian_symm : ∀ ι' ι, abelianHessianKernel θ ι' ι = abelianHessianKernel θ ι ι'
end Kernels
section Charges
def constGauge (L : ℕ) (ϑ : ℝ) : FullSpace.Vertex L 0 0 → ComplexMatrix2 := fun _ => cartanPhase ϑ
structure ChargeSymmetries (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop where
  cartanPhase_mem : ∀ ϑ : ℝ, cartanPhase ϑ ∈ PeriodicLattice.compactGaugeGroup
  constGauge_mem : ∀ ϑ : ℝ, constGauge L ϑ ∈ FullSpace.gaugeGroupAt L 0 0
  laplacian_comm : ∀ (ϑ : ℝ) (l : FullSpace.Vertex L 0 0 → ComplexMatrix2), IsL2Traceless l →
    FullSpace.abelianGaugeLaplacian θ (FullSpace.adjointVertexFn (constGauge L ϑ) l) =
      FullSpace.adjointVertexFn (constGauge L ϑ) (FullSpace.abelianGaugeLaplacian θ l)
  hessian_comm : ∀ ϑ : ℝ, ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    FullSpace.abelianMassiveHessian θ (FullSpace.adjointForm (constGauge L ϑ) B) =
      FullSpace.adjointForm (constGauge L ϑ) (FullSpace.abelianMassiveHessian θ B)
  laplacian_neutral : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2, IsL2Traceless l →
    IsNeutral l → IsNeutral (FullSpace.abelianGaugeLaplacian θ l)
  laplacian_pos : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2, IsL2Traceless l →
    IsPositivelyCharged l → IsPositivelyCharged (FullSpace.abelianGaugeLaplacian θ l)
  laplacian_neg : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2, IsL2Traceless l →
    IsNegativelyCharged l → IsNegativelyCharged (FullSpace.abelianGaugeLaplacian θ l)
  hessian_neutral : ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    IsNeutral (FullSpace.restrictToPositiveEdges B) →
      IsNeutral (FullSpace.restrictToPositiveEdges (FullSpace.abelianMassiveHessian θ B))
  hessian_pos : ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    IsPositivelyCharged (FullSpace.restrictToPositiveEdges B) →
      IsPositivelyCharged (FullSpace.restrictToPositiveEdges (FullSpace.abelianMassiveHessian θ B))
  hessian_neg : ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    IsNegativelyCharged (FullSpace.restrictToPositiveEdges B) →
      IsNegativelyCharged (FullSpace.restrictToPositiveEdges (FullSpace.abelianMassiveHessian θ B))
  star_vertex_l2 : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2, IsL2Traceless l →
    IsL2Traceless (fieldStar l)
  star_form_l2 : ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    fieldStar B ∈ FullSpace.l2Forms (meshAt L 0 0)
  laplacian_star : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2, IsL2Traceless l →
    FullSpace.abelianGaugeLaplacian θ (fieldStar l) = fieldStar (FullSpace.abelianGaugeLaplacian θ l)
  hessian_star : ∀ B ∈ FullSpace.l2Forms (meshAt L 0 0),
    FullSpace.abelianMassiveHessian θ (fieldStar B) =
      fieldStar (FullSpace.abelianMassiveHessian θ B)
  star_vertex_pos : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
    IsPositivelyCharged l → IsNegativelyCharged (fieldStar l)
  star_vertex_neg : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
    IsNegativelyCharged l → IsPositivelyCharged (fieldStar l)
  star_form_pos : ∀ B : FullSpace.Edge L 0 0 → ComplexMatrix2,
    IsPositivelyCharged (FullSpace.restrictToPositiveEdges B) →
      IsNegativelyCharged (FullSpace.restrictToPositiveEdges (fieldStar B))
  star_form_neg : ∀ B : FullSpace.Edge L 0 0 → ComplexMatrix2,
    IsNegativelyCharged (FullSpace.restrictToPositiveEdges B) →
      IsPositivelyCharged (FullSpace.restrictToPositiveEdges (fieldStar B))
def covShift (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (μ : Fin 4) :
    ScalarL2 L →L[ℂ] ScalarL2 L :=
  Classical.epsilon fun T => ∀ (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
    T w x 0 = FullSpace.chargedShift θ μ (fun y => w y 0) x
def covShiftSubOne (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (μ : Fin 4)
    (w : ScalarL2 L) : ScalarL2 L :=
  (covShift θ μ - ContinuousLinearMap.id ℂ (ScalarL2 L)) w
def covShiftAdjSubOne (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (μ : Fin 4)
    (w : ScalarL2 L) : ScalarL2 L :=
  (opAdjoint (covShift θ μ) - ContinuousLinearMap.id ℂ (ScalarL2 L)) w
def raisingVertexFn (w : ScalarL2 L) : FullSpace.Vertex L 0 0 → ComplexMatrix2 :=
  fun x => w x 0 • raisingPauli
def IsRaisingFormOf (W : Fin 4 → ScalarL2 L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) ∧
    ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = W μ x 0 • raisingPauli
structure CovariantShifts (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop where
  covShift_apply : ∀ (μ : Fin 4) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
    covShift θ μ w x 0 = FullSpace.chargedShift θ μ (fun y => w y 0) x
  covShift_unitary : ∀ μ : Fin 4, UnitaryCombinations.IsUnitaryOp
    (covShift θ μ : ScalarL2 L →ₗ[ℂ] ScalarL2 L)
  existsUnique_forwardEdge : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
    ∃! c : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge c.1 c.2 = b
  raisingVertexFn_l2 : ∀ w : ScalarL2 L, IsL2Traceless (raisingVertexFn w)
  exists_raisingForm : ∀ W : Fin 4 → ScalarL2 L, ∃ B, IsRaisingFormOf W B
  raisingForm_l2 : ∀ (W : Fin 4 → ScalarL2 L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2),
    IsRaisingFormOf W B → B ∈ FullSpace.l2Forms (meshAt L 0 0)
  covDiff_raising : ∀ (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
    FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w)
        (InfiniteLattice.Link.forwardFrom x μ) = covShiftSubOne θ μ w x 0 • raisingPauli
  covDiffAdjoint_raising : ∀ (W : Fin 4 → ScalarL2 L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2),
    IsRaisingFormOf W B → ∀ x : FullSpace.Vertex L 0 0,
      FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x =
        (∑ μ, covShiftAdjSubOne θ μ (W μ) x 0) • raisingPauli
end Charges
section Plaquettes
variable {a : ℝ}
def facePositiveEdge (p : InfiniteLattice.ElementaryPlaquette a) :
    Fin 4 → FullSpace.PositiveEdge a :=
  ![FullSpace.forwardEdge p.corner p.lowAxis,
    FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis,
    FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis,
    FullSpace.forwardEdge p.corner p.highAxis]
theorem facePositiveEdge_val (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    (facePositiveEdge p i).1 = FullSpace.faceEdge p i := by
  fin_cases i <;> rfl
end Plaquettes
structure FaceVariables (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop where
  abelianLinkField_mem : FullSpace.abelianLinkField θ ∈ FullSpace.fieldSpace L 0 0
  faceVariable_eq : ∀ p : FullSpace.Face L 0 0,
    FullSpace.faceVariable (FullSpace.abelianLinkField θ) p =
      cartanPhase (FullSpace.faceAngle θ p)
  half_fullTrace : ∀ p : FullSpace.Face L 0 0,
    (1 / 2 : ℂ) * ComplexMatrix2.fullTrace (FullSpace.faceVariable (FullSpace.abelianLinkField θ) p) =
      ((Real.cos (FullSpace.faceAngle θ p) : ℝ) : ℂ)
  faceVariable_sub_inv : ∀ p : FullSpace.Face L 0 0,
    FullSpace.faceVariable (FullSpace.abelianLinkField θ) p -
        (FullSpace.faceVariable (FullSpace.abelianLinkField θ) p)⁻¹ =
      (2 * Complex.I * ((Real.sin (FullSpace.faceAngle θ p) : ℝ) : ℂ)) • ComplexMatrix2.pauliFamily 2
  transportedForm_eq : ∀ B ∈ FullSpace.edgeFormSpace (meshAt L 0 0), ∀ (p : FullSpace.Face L 0 0)
    (i : Fin 4),
    FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i =
      (transportSign i * ((FullSpace.diagonalComponent B (facePositiveEdge p i) : ℝ) : ℂ)) •
          ComplexMatrix2.pauliFamily 2 +
        FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i • raisingPauli +
        conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) • loweringPauli
  lie_trace : ∀ B ∈ FullSpace.edgeFormSpace (meshAt L 0 0), ∀ (p : FullSpace.Face L 0 0)
    (i j : Fin 4),
    (Complex.I / 2) * ComplexMatrix2.fullTrace
        (⁅FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i,
          FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p j⁆ *
          ComplexMatrix2.pauliFamily 2) =
      ((-2 * (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i *
        conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p j)).im : ℝ) : ℂ)
section Form
def toScalarL2 (v : FullSpace.Vertex L 0 0 → ℂ) : ScalarL2 L :=
  Classical.epsilon fun w => ∀ x, w x 0 = v x
def faceTerm (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0) : ℝ :=
  Real.cos (FullSpace.faceAngle θ p) *
      (FullSpace.edgeDifference (FullSpace.diagonalComponent B) p ^ 2 +
        ‖∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i‖ ^ 2) -
    2 * Real.sin (FullSpace.faceAngle θ p) *
      ∑ c ∈ Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2),
        (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p c.1 *
          conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p c.2)).im
def vertexTerm (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) (x : FullSpace.Vertex L 0 0) : ℝ :=
  FullSpace.vertexAdjoint (FullSpace.diagonalComponent B) x ^ 2 +
    ‖∑ μ, covShiftAdjSubOne θ μ
      (toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ)) x 0‖ ^ 2
def HessianQuadraticForm (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace (meshAt L 0 0), FullSpace.HasFiniteEdgeSupport B →
    (∀ (μ : Fin 4) (x : FullSpace.Vertex L 0 0),
      toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ) x 0 =
        FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ x) ∧
    (Function.support (faceTerm θ B)).Finite ∧
    (Function.support (vertexTerm θ B)).Finite ∧
    FullSpace.finiteEdgePairing B (FullSpace.abelianMassiveHessian θ B) =
      ((∑ᶠ p, faceTerm θ B p + ∑ᶠ x, vertexTerm θ B x : ℝ) : ℂ)
def SpectralLowerBounds (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop :=
  ((∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle θ p| ≤ Real.pi / 2) →
    IsBoundedBelowBy (AbelianFieldDensity.massiveOp θ)
      (-24 * ⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)|)) ∧
  IsBoundedBelowBy (laplacianOp θ) 0
def ActionDerivative (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace (meshAt L 0 0), FullSpace.HasFiniteEdgeSupport B →
    (Function.support fun p : FullSpace.Face L 0 0 =>
      Real.sin (FullSpace.faceAngle θ p) *
        FullSpace.edgeDifference (FullSpace.diagonalComponent B) p).Finite ∧
    FullSpace.complexActionDeriv (FullSpace.abelianLinkField θ) B =
      ((∑ᶠ p : FullSpace.Face L 0 0, Real.sin (FullSpace.faceAngle θ p) *
        FullSpace.edgeDifference (FullSpace.diagonalComponent B) p : ℝ) : ℂ)
end Form
def LinearFieldAngles (L : ℕ) : Prop :=
  ∀ (f : ℝ) (p : FullSpace.Face L 0 0),
    FullSpace.faceAngle (fun b => f * FullSpace.linearAbelianAngle b) p =
      if p.lowAxis = 0 ∧ p.highAxis = 1 then f else 0
end AbelianFieldFacts
end Tower
end YangMills.Construction
end
