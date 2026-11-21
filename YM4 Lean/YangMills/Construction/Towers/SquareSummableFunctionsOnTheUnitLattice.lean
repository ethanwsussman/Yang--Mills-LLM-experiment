import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctions
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace UnitLatticeL2
section Preliminaries
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']
def IsAdjointOp (Z : H →L[ℂ] H') (A : H' →L[ℂ] H) : Prop :=
  ∀ (ψ : H') (χ : H), inner ℂ (A ψ) χ = inner ℂ ψ (Z χ)
def IsBoundedBelowBy (T : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∀ ψ : H, (inner ℂ ψ (T ψ) - (c : ℂ) * inner ℂ ψ ψ).im = 0 ∧
    0 ≤ (inner ℂ ψ (T ψ) - (c : ℂ) * inner ℂ ψ ψ).re
variable [CompleteSpace H] [CompleteSpace H']
def opAdjoint (Z : H →L[ℂ] H') : H' →L[ℂ] H := ContinuousLinearMap.adjoint Z
def IsSelfAdjointOp (T : H →L[ℂ] H) : Prop := opAdjoint T = T
end Preliminaries
def AdjointCharacterization : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (Z : H →L[ℂ] H'),
    IsAdjointOp Z (opAdjoint Z) ∧ ∀ A : H' →L[ℂ] H, IsAdjointOp Z A → A = opAdjoint Z
section Functions
variable {σ : Type}
def pauliCoeffs (X : Matrices.ComplexMatrix2) : Fin 3 → ℂ :=
  Classical.epsilon fun c : Fin 3 → ℂ => X = ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a
def coordAt (f : σ → Matrices.ComplexMatrix2) (ι : Fin 3 × σ) : ℂ := pauliCoeffs (f ι.2) ι.1
abbrev L2Field (σ : Type) : Type := lp (fun _ : Fin 3 × σ => ℂ) 2
def ofCoords (v : Fin 3 × σ → ℂ) : σ → Matrices.ComplexMatrix2 :=
  fun s => ∑ a, v (a, s) • Matrices.ComplexMatrix2.pauliFamily a
def fieldStar (f : σ → Matrices.ComplexMatrix2) : σ → Matrices.ComplexMatrix2 :=
  fun s => Matrices.ComplexMatrix2.adjointMatrix (f s)
def fieldNorm (f : σ → Matrices.ComplexMatrix2) : ℝ := Real.sqrt (Tower.hermitianInner f f).re
open Classical in
def basisVec {J : Type} (ι : J) : lp (fun _ : J => ℂ) 2 := lp.single 2 ι (1 : ℂ)
def matrixEntry {J : Type} (S : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2) (ι' ι : J) : ℂ :=
  S (basisVec ι) ι'
def opOfMap (M : (σ → Matrices.ComplexMatrix2) → σ → Matrices.ComplexMatrix2) :
    L2Field σ →L[ℂ] L2Field σ :=
  Classical.epsilon fun T => ∀ v : L2Field σ,
    ofCoords (T v) = M (ofCoords v)
variable (σ)
def CoordsIsometry : Prop :=
  (∀ f : σ → Matrices.ComplexMatrix2, (∀ s, f s ∈ Matrices.ComplexMatrix2.traceless) →
    (Tower.IsL2Traceless f ↔ Summable fun ι => ‖coordAt f ι‖ ^ 2)) ∧
  (∀ f f' : σ → Matrices.ComplexMatrix2, Tower.IsL2Traceless f → Tower.IsL2Traceless f' →
    Summable (fun ι => ‖conj (coordAt f ι) * coordAt f' ι‖) ∧
      Tower.hermitianInner f f' = ∑' ι, conj (coordAt f ι) * coordAt f' ι) ∧
  (∀ v : L2Field σ, Tower.IsL2Traceless (ofCoords v) ∧
    ∀ ι, coordAt (ofCoords v) ι = v ι) ∧
  (∀ f : σ → Matrices.ComplexMatrix2, Tower.IsL2Traceless f →
    ∃ v : L2Field σ, ofCoords v = f) ∧
  (∀ (c : ℂ) (v v' : L2Field σ),
    ofCoords (v + v' : L2Field σ) = ofCoords v + ofCoords v' ∧
      ofCoords (c • v : L2Field σ) = c • ofCoords v) ∧
  ∀ v v' : L2Field σ,
    Tower.hermitianInner (ofCoords v) (ofCoords v') = inner ℂ v v'
def StarProperties : Prop :=
  ∀ f : σ → Matrices.ComplexMatrix2, Tower.IsL2Traceless f →
    (∀ s, Matrices.ComplexMatrix2.adjointMatrix (f s) ∈ Matrices.ComplexMatrix2.traceless) ∧
    (∀ ι, coordAt (fieldStar f) ι = conj (coordAt f ι)) ∧
    Tower.IsL2Traceless (fieldStar f) ∧
    fieldNorm (fieldStar f) = fieldNorm f
def ScalarMultipleInner : Prop :=
  ∀ X ∈ Matrices.ComplexMatrix2.traceless, ∀ s s' : σ → ℂ,
    Summable (fun i => ‖s i‖ ^ 2) → Summable (fun i => ‖s' i‖ ^ 2) →
    Tower.IsL2Traceless (fun i => s i • X) ∧ Tower.IsL2Traceless (fun i => s' i • X) ∧
    Tower.hermitianInner (fun i => s i • X) (fun i => s' i • X) =
      Matrices.ComplexMatrix2.halfTrace (Matrices.ComplexMatrix2.adjointMatrix X * X) *
        ∑' i, conj (s i) * s' i
end Functions
section Kernels
variable {J : Type}
def MatrixEntryProperties (J : Type) : Prop :=
  ∀ S : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2,
    (∀ ι' ι, matrixEntry S ι' ι = inner ℂ (basisVec ι') (S (basisVec ι)) ∧
      ‖matrixEntry S ι' ι‖ ≤ ‖S‖) ∧
    ∀ (f : lp (fun _ : J => ℂ) 2) (ι' : J),
      Summable (fun ι => ‖matrixEntry S ι' ι * f ι‖) ∧ S f ι' = ∑' ι, matrixEntry S ι' ι * f ι
def BoundedKernelOperator (position : J → InfiniteLattice.AmbientSpace) : Prop :=
  ∀ (C : ℝ) (M : J → J → ℂ), (∀ ι' ι, ‖M ι' ι‖ ≤ C) →
    (∀ ι' ι, ¬ TorusMetric.euclidNormVec (position ι' - position ι) ≤ 2 → M ι' ι = 0) →
    ∃ T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2,
      (∀ (f : lp (fun _ : J => ℂ) 2) (ι' : J),
        {ι | M ι' ι * f ι ≠ 0}.Finite ∧ {ι | M ι' ι * f ι ≠ 0}.ncard ≤ 12 * 5 ^ 4 ∧
          T f ι' = ∑' ι, M ι' ι * f ι) ∧
      ‖T‖ ≤ 12 * 5 ^ 4 * C ∧
      ((∀ ι' ι, M ι ι' = conj (M ι' ι)) → IsSelfAdjointOp T)
end Kernels
section Lattice
variable (L : ℕ)
abbrev VertexIndex : Type := Fin 3 × Tower.FullSpace.Vertex L 0 0
abbrev EdgeIndex : Type := Fin 3 × PeriodicOperators.PosEdge L 0 0
def vertexPos : VertexIndex L → InfiniteLattice.AmbientSpace :=
  (PeriodicOperators.colourVertices L 0 0).pos
def edgePos : EdgeIndex L → InfiniteLattice.AmbientSpace :=
  (PeriodicOperators.colourEdges L 0 0).pos
abbrev VectorL2 (N' : ℕ) : Type :=
  lp (fun _ : Tower.FullSpace.Vertex L 0 0 => EuclideanSpace ℂ (Fin N')) 2
def VectorL2Description (N' : ℕ) : Prop :=
  (∀ v : Tower.FullSpace.Vertex L 0 0 → EuclideanSpace ℂ (Fin N'),
    Memℓp v 2 ↔ Summable fun x => ∑ i, ‖v x i‖ ^ 2) ∧
  ∀ v v' : VectorL2 L N',
    Summable (fun x => ‖∑ i, conj (v x i) * v' x i‖) ∧
      inner ℂ v v' = ∑' x, ∑ i, conj (v x i) * v' x i
def VertexIndexCount : Prop :=
  (∀ x : Tower.FullSpace.Vertex L 0 0,
    {ι : VertexIndex L | vertexPos L ι = x} = Set.range (fun a : Fin 3 => (a, x)) ∧
      (Set.range (fun a : Fin 3 => ((a, x) : VertexIndex L))).ncard = 3) ∧
  ∀ y : Tower.FullSpace.Vertex L 0 0,
    {ι : VertexIndex L | TorusMetric.euclidNormVec (vertexPos L ι - y) ≤ 2}.Finite ∧
      {ι : VertexIndex L | TorusMetric.euclidNormVec (vertexPos L ι - y) ≤ 2}.ncard ≤ 12 * 5 ^ 4
def EdgeIndexCount : Prop :=
  (∀ x : Tower.FullSpace.Vertex L 0 0,
    {ι : EdgeIndex L | edgePos L ι = x} =
        Set.range (fun c : Fin 3 × Fin 4 => (c.1, Tower.FullSpace.forwardEdge x c.2)) ∧
      (Set.range (fun c : Fin 3 × Fin 4 =>
        ((c.1, Tower.FullSpace.forwardEdge x c.2) : EdgeIndex L))).ncard = 12) ∧
  ∀ y : Tower.FullSpace.Vertex L 0 0,
    {ι : EdgeIndex L | TorusMetric.euclidNormVec (edgePos L ι - y) ≤ 2}.Finite ∧
      {ι : EdgeIndex L | TorusMetric.euclidNormVec (edgePos L ι - y) ≤ 2}.ncard ≤ 12 * 5 ^ 4
end Lattice
end UnitLatticeL2
open UnitLatticeL2 in
def UnitLatticeL2Statement : Prop :=
  AdjointCharacterization ∧
  ∀ L : ℕ,
    (∀ N' : ℕ, 1 ≤ N' → VectorL2Description L N') ∧
    (CoordsIsometry (Tower.FullSpace.Vertex L 0 0) ∧ StarProperties (Tower.FullSpace.Vertex L 0 0) ∧
      ScalarMultipleInner (Tower.FullSpace.Vertex L 0 0) ∧ VertexIndexCount L ∧
      MatrixEntryProperties (VertexIndex L) ∧ BoundedKernelOperator (vertexPos L)) ∧
    (CoordsIsometry (PeriodicOperators.PosEdge L 0 0) ∧
      StarProperties (PeriodicOperators.PosEdge L 0 0) ∧
      ScalarMultipleInner (PeriodicOperators.PosEdge L 0 0) ∧ EdgeIndexCount L ∧
      MatrixEntryProperties (EdgeIndex L) ∧ BoundedKernelOperator (edgePos L))
end Tower
end YangMills.Construction
end
