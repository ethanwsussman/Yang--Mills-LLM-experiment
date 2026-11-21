import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.MatricesThatMultiplyTheCoefficients
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaveCalculus
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (QuotHom IsFiniteRange PeriodicData IsQuasiPeriodic KernelMatrix
  descendFn
  quotHomInverse quotHomTranspose colourEdges colourFaces colourVertices toComplexVec
  openImStrip bilinDot linearMapEntry wNorm wInner compKernel wPairing
  phaseMul castVec symbolHom kernelTranspose)
open PeriodicOperators.Quotients (conjKernel)
open PlaneWaves
def expWave (q : Fin 4 → ℂ) (x : AmbientSpace) : ℂ :=
  Complex.exp (Complex.I * bilinDot q (toComplexVec x))
def integerWave (m : Fin 4 → ℤ) (x : AmbientSpace) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * bilinDot (toComplexVec (castVec m)) (toComplexVec x))
def tracelessPairing (A B : Matrices.ComplexMatrix2) : ℂ :=
  open Classical in
  if h : A ∈ Matrices.ComplexMatrix2.traceless ∧ B ∈ Matrices.ComplexMatrix2.traceless then
    OneLoop.traceForm ⟨A, h.1⟩ ⟨B, h.2⟩ else 0
def posEdgeAt (L k j : ℕ) (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    PeriodicOperators.PosEdge L k j :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def topVertexElement (L k : ℕ) (g : (colourVertices L k k).UnitQuot → ℂ) :
    Matrices.ComplexMatrix2 :=
  ofPauliCoeffs (fun ι : Fin 3 × FullSpace.Vertex L k k => g ((colourVertices L k k).mkQuot 1 ι)) 0
def topEdgeComponent (L k : ℕ) (z : (colourEdges L k k).UnitQuot → ℂ) (μ : Fin 4) :
    Matrices.ComplexMatrix2 :=
  ofPauliCoeffs
    (fun ι : Fin 3 × PeriodicOperators.PosEdge L k k =>
      z ((colourEdges L k k).mkQuot 1 ι))
    (posEdgeAt L k k 0 μ)
abbrev AxisPair : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}
def waveOnQuot (I : PeriodicData) (carries : I.Carrier → Prop) (m : Fin 4 → ℤ) : I.UnitQuot → ℂ :=
  open Classical in
  descendFn I fun ι => if carries ι then integerWave m (I.pos ι) else 0
open Classical in
def WavesOrthonormalBasis (L k : ℕ) (I : PeriodicData) {C : Type}
    (carries : C → I.Carrier → Prop) : Prop :=
  (∀ c c' : C, ∀ m ∈ freqBox L k, ∀ m' ∈ freqBox L k,
    wInner (I.quotWeight 1) (waveOnQuot I (carries c) m)
        (waveOnQuot I (carries c') m') = if c = c' ∧ m = m' then 1 else 0) ∧
  Submodule.span ℂ {f | ∃ c : C, ∃ m ∈ freqBox L k, f = waveOnQuot I (carries c) m} = ⊤
structure VertexCoeffFacts (L k : ℕ) : Prop where
  basis : WavesOrthonormalBasis L k (colourVertices L k 0) fun (a : Fin 3) ι => ι.1 = a
  expansion : ∀ (l : (colourVertices L k 0).UnitQuot → ℂ) (x : FullSpace.Vertex L k 0),
    vertexFieldOfClasses L k l x =
      ∑ m ∈ freqBox L k, integerWave m x • vertexFourierCoeff L k l m
  exp_expansion : ∀ (κ : Fin 4 → ℂ) (l : (colourVertices L k 0).UnitQuot → ℂ)
    (x : FullSpace.Vertex L k 0),
    expWave κ x • vertexFieldOfClasses L k l x =
      ∑ m ∈ freqBox L k, expWave (shiftedFreq κ m) x • vertexFourierCoeff L k l m
  norm_sq : ∀ l : (colourVertices L k 0).UnitQuot → ℂ,
    wNorm ((colourVertices L k 0).quotWeight 1) l ^ 2 =
      ∑ m ∈ freqBox L k, pauliNorm (vertexFourierCoeff L k l m) ^ 2
  pairing_eq : ∀ l l' : (colourVertices L k 0).UnitQuot → ℂ,
    wPairing ((colourVertices L k 0).quotWeight 1) l l' =
      ∑ m ∈ freqBox L k,
        tracelessPairing (vertexFourierCoeff L k l m) (vertexFourierCoeff L k l' (-m))
structure EdgeCoeffFacts (L k : ℕ) : Prop where
  basis : WavesOrthonormalBasis L k (colourEdges L k 0)
    fun (c : Fin 3 × Fin 4) ι => ι.1 = c.1 ∧ ∃ x, ι.2 = posEdgeAt L k 0 x c.2
  expansion : ∀ (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (x : FullSpace.Vertex L k 0),
    edgeFieldOfClasses L k b (edgeAt L k x μ) =
      ∑ m ∈ freqBox L k, integerWave m x • edgeFourierCoeff L k b μ m
  exp_expansion : ∀ (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4)
    (x : FullSpace.Vertex L k 0),
    expWave κ x • edgeFieldOfClasses L k b (edgeAt L k x μ) =
      ∑ m ∈ freqBox L k, expWave (shiftedFreq κ m) x • edgeFourierCoeff L k b μ m
  norm_sq : ∀ b : (colourEdges L k 0).UnitQuot → ℂ,
    wNorm ((colourEdges L k 0).quotWeight 1) b ^ 2 =
      ∑ m ∈ freqBox L k, ∑ μ, pauliNorm (edgeFourierCoeff L k b μ m) ^ 2
  pairing_eq : ∀ b b' : (colourEdges L k 0).UnitQuot → ℂ,
    wPairing ((colourEdges L k 0).quotWeight 1) b b' =
      ∑ m ∈ freqBox L k, ∑ μ,
        tracelessPairing (edgeFourierCoeff L k b μ m) (edgeFourierCoeff L k b' μ (-m))
structure FaceCoeffFacts (L k : ℕ) : Prop where
  basis : WavesOrthonormalBasis L k (colourFaces L k 0)
    fun (c : Fin 3 × AxisPair) ι =>
      ι.1 = c.1 ∧ ι.2.lowAxis = c.2.1.1 ∧ ι.2.highAxis = c.2.1.2
  expansion : ∀ (f : (colourFaces L k 0).UnitQuot → ℂ) (μ ν : Fin 4) (h : μ < ν)
    (x : FullSpace.Vertex L k 0),
    faceFieldOfClasses L k f ⟨x, μ, ν, h⟩ =
      ∑ m ∈ freqBox L k, integerWave m x • faceFourierCoeff L k f μ ν h m
  exp_expansion : ∀ (κ : Fin 4 → ℂ) (f : (colourFaces L k 0).UnitQuot → ℂ) (μ ν : Fin 4)
    (h : μ < ν) (x : FullSpace.Vertex L k 0),
    expWave κ x • faceFieldOfClasses L k f ⟨x, μ, ν, h⟩ =
      ∑ m ∈ freqBox L k, expWave (shiftedFreq κ m) x • faceFourierCoeff L k f μ ν h m
  norm_sq : ∀ f : (colourFaces L k 0).UnitQuot → ℂ,
    wNorm ((colourFaces L k 0).quotWeight 1) f ^ 2 =
      ∑ m ∈ freqBox L k, ∑ p : AxisPair,
        pauliNorm (faceFourierCoeff L k f p.1.1 p.1.2 p.2 m) ^ 2
  pairing_eq : ∀ f f' : (colourFaces L k 0).UnitQuot → ℂ,
    wPairing ((colourFaces L k 0).quotWeight 1) f f' =
      ∑ m ∈ freqBox L k, ∑ p : AxisPair,
        tracelessPairing (faceFourierCoeff L k f p.1.1 p.1.2 p.2 m)
          (faceFourierCoeff L k f' p.1.1 p.1.2 p.2 (-m))
abbrev meshC (L k : ℕ) : ℂ := ((finestMesh L k : ℝ) : ℂ)
def periodShift (L k : ℕ) (q : Fin 4 → ℂ) (e : Fin 4 → ℤ) : Fin 4 → ℂ :=
  fun μ => q μ + 2 * (Real.pi : ℂ) / meshC L k * (e μ : ℂ)
def conjVec (q : Fin 4 → ℂ) : Fin 4 → ℂ := fun μ => conj (q μ)
structure SymbolFormulas (L k : ℕ) : Prop where
  symbolSquare_eq : ∀ q : Fin 4 → ℂ, symbolSquare L k q =
    ∑ μ, 2 * (meshC L k)⁻¹ ^ 2 * (1 - Complex.cos (meshC L k * q μ))
  symbolSquare_neg : ∀ q : Fin 4 → ℂ, symbolSquare L k (-q) = symbolSquare L k q
  symbolSquare_periodic : ∀ (q : Fin 4 → ℂ) (e : Fin 4 → ℤ),
    symbolSquare L k (periodShift L k q e) = symbolSquare L k q
  conj_symbolSquare : ∀ q : Fin 4 → ℂ,
    conj (symbolSquare L k q) = symbolSquare L k (conjVec q)
  symbolSquare_ofReal : ∀ q' : AmbientSpace, symbolSquare L k (toComplexVec q') =
    ∑ ν, ((‖forwardSymbol L k (toComplexVec q') ν‖ ^ 2 : ℝ) : ℂ)
  sin_mul_dirichletSum : ∀ τ : ℂ,
    (meshC L k)⁻¹ * Complex.sin (meshC L k * τ / 2) * dirichletSum L k τ =
      Complex.sin (τ / 2)
  dirichletSum_neg : ∀ τ : ℝ, dirichletSum L k (-(τ : ℂ)) = dirichletSum L k (τ : ℂ)
  dirichletSum_im : ∀ τ : ℝ, (dirichletSum L k (τ : ℂ)).im = 0
  geom_sum_eq : ∀ τ : ℂ,
    meshC L k * ∑ l ∈ Finset.range (L ^ k),
        Complex.exp (Complex.I * meshC L k * (l : ℂ) * τ) =
      Complex.exp (Complex.I * (1 - meshC L k) * τ / 2) * dirichletSum L k τ
structure WeightRelations (L k : ℕ) : Prop where
  edgeWeight_mul_forwardSymbol : ∀ (q : Fin 4 → ℂ) (μ : Fin 4),
    edgeWeight L k q μ * forwardSymbol L k q μ = unitSymbol q μ * PlaneWaves.vertexWeight L k q
  unitSymbol_shiftedFreq : ∀ (κ : Fin 4 → ℂ), ∀ m ∈ freqBox L k,
    unitSymbol (shiftedFreq κ m) = unitSymbol κ
  vertexWeight_neg : ∀ q : AmbientSpace,
    PlaneWaves.vertexWeight L k (-toComplexVec q) = PlaneWaves.vertexWeight L k (toComplexVec q)
  vertexWeight_im : ∀ q : AmbientSpace, (PlaneWaves.vertexWeight L k (toComplexVec q)).im = 0
abbrev freeOps (L k : ℕ) := FullSpace.rescaledOperators L k fun _ => 1
abbrev vertexCoboundaryT (L k j : ℕ) :=
  kernelTranspose (colourVertices L k j) (colourEdges L k j)
    (FullSpace.scaledVertexCoboundaryKernel L k j)
abbrev edgeCoboundaryT (L k j : ℕ) :=
  kernelTranspose (colourEdges L k j) (colourFaces L k j)
    (FullSpace.scaledEdgeCoboundaryKernel L k j)
structure CoboundarySymbols (L k : ℕ) : Prop where
  vertexCoboundary : ∀ (κ : Fin 4 → ℂ) (l : (colourVertices L k 0).UnitQuot → ℂ) (μ : Fin 4),
    ∀ m ∈ freqBox L k,
      edgeFourierCoeff L k
          (symbolHom (colourVertices L k 0) (colourEdges L k 0)
            (FullSpace.scaledVertexCoboundaryKernel L k 0) κ l) μ m =
        forwardSymbol L k (shiftedFreq κ m) μ • vertexFourierCoeff L k l m
  edgeCoboundary : ∀ (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ ν : Fin 4)
    (h : μ < ν), ∀ m ∈ freqBox L k,
      faceFourierCoeff L k
          (symbolHom (colourEdges L k 0) (colourFaces L k 0)
            (FullSpace.scaledEdgeCoboundaryKernel L k 0) κ b) μ ν h m =
        forwardSymbol L k (shiftedFreq κ m) μ • edgeFourierCoeff L k b ν m -
          forwardSymbol L k (shiftedFreq κ m) ν • edgeFourierCoeff L k b μ m
  vertexCoboundary_transpose : ∀ (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ),
    ∀ m ∈ freqBox L k,
      vertexFourierCoeff L k
          (symbolHom (colourEdges L k 0) (colourVertices L k 0)
            (vertexCoboundaryT L k 0) κ b) m =
        ∑ μ, forwardSymbol L k (-shiftedFreq κ m) μ • edgeFourierCoeff L k b μ m
  K : ∀ κ : Fin 4 → ℂ, ScalesEdgeCoeffs L k (symbolSquare L k) κ
    (symbolHom (colourEdges L k 0) (colourEdges L k 0) (freeOps L k).K κ)
  Delta : ∀ κ : Fin 4 → ℂ, ScalesVertexCoeffs L k (symbolSquare L k) κ
    (symbolHom (colourVertices L k 0) (colourVertices L k 0) (freeOps L k).Delta κ)
  coboundary_comp_coboundary : compKernel (FullSpace.scaledEdgeCoboundaryKernel L k 0)
    (FullSpace.scaledVertexCoboundaryKernel L k 0) = 0
  transpose_comp_transpose : compKernel (vertexCoboundaryT L k 0)
    (edgeCoboundaryT L k 0) = 0
structure SmoothingSymbols (L k : ℕ) : Prop where
  R : ∀ (κ : Fin 4 → ℂ) (l : (colourVertices L k 0).UnitQuot → ℂ),
    topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R κ l) =
      ∑ m ∈ freqBox L k,
        PlaneWaves.vertexWeight L k (shiftedFreq κ m) • vertexFourierCoeff L k l m
  Q : ∀ (κ : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4),
    topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q κ b) μ =
      ∑ m ∈ freqBox L k, edgeWeight L k (shiftedFreq κ m) μ • edgeFourierCoeff L k b μ m
  Rt : ∀ (κ : Fin 4 → ℂ) (g : (colourVertices L k k).UnitQuot → ℂ),
    ∀ m ∈ freqBox L k,
      vertexFourierCoeff L k
          (symbolHom (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt κ g) m =
        PlaneWaves.vertexWeight L k (-shiftedFreq κ m) • topVertexElement L k g
  Qt : ∀ (κ : Fin 4 → ℂ) (z : (colourEdges L k k).UnitQuot → ℂ) (μ : Fin 4),
    ∀ m ∈ freqBox L k,
      edgeFourierCoeff L k
          (symbolHom (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt κ z) μ m =
        edgeWeight L k (-shiftedFreq κ m) μ • topEdgeComponent L k z μ
def IsRealColourTrivial {σ σ' : Type} (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Prop :=
  (∀ ι' ι, (T ι' ι).im = 0) ∧ IsColourTrivial T
structure FreeOpsRealFiniteRange (L k : ℕ) : Prop where
  vertexCoboundary : ∀ j : ℕ, j ≤ k →
    IsFiniteRange (colourVertices L k j) (colourEdges L k j)
      (FullSpace.scaledVertexCoboundaryKernel L k j) ∧
    IsRealColourTrivial (FullSpace.scaledVertexCoboundaryKernel L k j)
  edgeCoboundary : ∀ j : ℕ, j ≤ k →
    IsFiniteRange (colourEdges L k j) (colourFaces L k j)
      (FullSpace.scaledEdgeCoboundaryKernel L k j) ∧
    IsRealColourTrivial (FullSpace.scaledEdgeCoboundaryKernel L k j)
  vertexCoboundary_transpose : ∀ j : ℕ, j ≤ k →
    IsFiniteRange (colourEdges L k j) (colourVertices L k j) (vertexCoboundaryT L k j) ∧
    IsRealColourTrivial (vertexCoboundaryT L k j)
  edgeCoboundary_transpose : ∀ j : ℕ, j ≤ k →
    IsFiniteRange (colourFaces L k j) (colourEdges L k j)
      (edgeCoboundaryT L k j) ∧
    IsRealColourTrivial (edgeCoboundaryT L k j)
  K : IsFiniteRange (colourEdges L k 0) (colourEdges L k 0) (freeOps L k).K ∧
    IsRealColourTrivial (freeOps L k).K
  Delta : IsFiniteRange (colourVertices L k 0) (colourVertices L k 0) (freeOps L k).Delta ∧
    IsRealColourTrivial (freeOps L k).Delta
  Q : IsFiniteRange (colourEdges L k 0) (colourEdges L k k) (freeOps L k).Q ∧
    IsRealColourTrivial (freeOps L k).Q
  R : IsFiniteRange (colourVertices L k 0) (colourVertices L k k) (freeOps L k).R ∧
    IsRealColourTrivial (freeOps L k).R
  Qt : IsFiniteRange (colourEdges L k k) (colourEdges L k 0) (freeOps L k).Qt ∧
    IsRealColourTrivial (freeOps L k).Qt
  Rt : IsFiniteRange (colourVertices L k k) (colourVertices L k 0) (freeOps L k).Rt ∧
    IsRealColourTrivial (freeOps L k).Rt
  Xi : IsFiniteRange (colourEdges L k 0) (colourEdges L k 0) (freeOps L k).Xi ∧
    IsRealColourTrivial (freeOps L k).Xi
  Y : IsFiniteRange (colourVertices L k 0) (colourVertices L k 0) (freeOps L k).Y ∧
    IsRealColourTrivial (freeOps L k).Y
  X : IsFiniteRange (colourEdges L k 0) (colourEdges L k 0) (freeOps L k).X ∧
    IsRealColourTrivial (freeOps L k).X
structure MultiplierMatrixFacts (I : PeriodicData) (Scales : (Fin 4 → ℂ) → QuotHom I I → Prop)
    (M : (Fin 4 → ℂ) → QuotHom I I) (υ : ℝ) (t : (Fin 4 → ℂ) → ℂ) : Prop where
  scales_unique : ∀ κ ∈ openImStrip υ,
    Scales κ (M κ) ∧ ∀ A, Scales κ A → A = M κ
  quasiPeriodic : IsQuasiPeriodic (openImStrip υ) M
  transpose_neg : (∀ q ∈ openImStrip υ, t (-q) = t q) →
    ∀ κ ∈ openImStrip υ, quotHomTranspose (M (-κ)) = M κ
  conj_entries : (∀ q ∈ openImStrip υ, t (-q) = t q) →
    (∀ q ∈ openImStrip υ, conj (t q) = t (conjVec q)) →
    ∀ κ ∈ openImStrip υ,
      conjKernel (linearMapEntry (M κ)) = linearMapEntry (M (-conjVec κ))
end YangMills.Construction.Tower.PlaneWaveCalculus
end
