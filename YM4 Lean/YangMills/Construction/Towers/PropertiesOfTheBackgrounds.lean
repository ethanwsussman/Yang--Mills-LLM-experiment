import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundProperties
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.ResponseProperties (ResponseBound)
open YangMills.Construction.PeriodicLattice (supOfOperatorNorms)
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators.JetDomains (fstMomentum sndMomentum)
def responseOnAxis (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (colourEdges L k 0).UnitQuot → ℂ :=
  symbolHom (colourEdges L k k) (colourEdges L k 0)
    (Tower.BackgroundFieldResponse.responseKernel L k) q
    (FullSpace.constantFormAmplitude L k (FullSpace.axisPauliElement μ 2))
def edgeCoboundarySymbol (L k : ℕ) (q : Fin 4 → ℂ) :
    QuotHom (colourEdges L k 0) (colourFaces L k 0) :=
  symbolHom (colourEdges L k 0) (colourFaces L k 0) (FullSpace.scaledEdgeCoboundaryKernel L k 0) q
open Classical in
def axisAmplitude (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (colourEdges L k 0).UnitQuot → ℂ :=
  if q ∈ momentumPolydisc stripHalfWidth then responseAmplitude L k q μ else responseOnAxis L k q μ
open Classical in
def axisCurvature (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (colourFaces L k 0).UnitQuot → ℂ :=
  if q ∈ momentumPolydisc stripHalfWidth then responseCurvature L k q μ
  else edgeCoboundarySymbol L k q (responseOnAxis L k q μ)
def axisField (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (Tower.remainderIndex L k).UnitQuot → ℂ :=
  ((Tower.finestMesh L k : ℝ) : ℂ) • axisAmplitude L k q μ
def axisJet {I I' : PeriodicData} (L k : ℕ)
    (T : ((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (p : Fin 4 → ℂ)
    (μPos μNeg : Fin 4) : JetQuad I I' :=
  jetAlong (Tower.remainderIndex L k) I I' T p (axisField L k p μPos) (axisField L k (-p) μNeg)
def jetWidth (p : Fin 4 → ℂ) : ℝ :=
  max stripHalfWidth (max |(p 0).im| (max |(p 1).im| (max |(p 2).im| |(p 3).im|)))
def ResponseSymbolSummableAt (L k : ℕ) (p : Fin 4 → ℂ) : Prop :=
  SymbolSummableAt (colourEdges L k k) (colourEdges L k 0)
      (Tower.BackgroundFieldResponse.responseKernel L k) p ∧
    SymbolSummableAt (colourEdges L k k) (colourEdges L k 0)
      (Tower.BackgroundFieldResponse.responseKernel L k) (-p)
theorem axisField_of_mem {L k : ℕ} {q : Fin 4 → ℂ} (hq : q ∈ momentumPolydisc stripHalfWidth)
    (μ : Fin 4) : axisField L k q μ = scaledResponseField L k q μ := by
  simp only [axisField, axisAmplitude, if_pos hq, scaledResponseField]
theorem axisJet_of_mem {I I' : PeriodicData} {L k : ℕ}
    (T : ((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) {p : Fin 4 → ℂ}
    (hp : p ∈ momentumPolydisc stripHalfWidth) (μPos μNeg : Fin 4) :
    axisJet L k T p μPos μNeg = jetAlongResponse L k T p μPos μNeg := by
  have hneg : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  simp only [axisJet, jetAlongResponse, axisField_of_mem hp, axisField_of_mem hneg]
def covDerivFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).D
def holonomyDefectFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourFaces L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => FullSpace.holonomyDefectKernel L k (gaugeFieldOfForm L k f)
def halfFaceTraceFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourFaces L k 0).Carrier → (colourFaces L k 0).Carrier → ℂ :=
  fun f => FullSpace.halfFaceTraceKernel L k (gaugeFieldOfForm L k f)
def curvatureFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => FullSpace.curvatureKernel (gaugeFieldOfForm L k f)
def edgeOperatorFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).K
def vertexOperatorFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourVertices L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).Delta
def edgeSmoothingFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).Q
def vertexSmoothingFn (L k : ℕ) : ((Tower.remainderIndex L k).Carrier → ℂ) →
    (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).R
def ForAllEight (L k : ℕ)
    (P : ∀ I I' : PeriodicData,
      (((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) → Prop) : Prop :=
  P (colourVertices L k 0) (colourEdges L k 0) (covDerivFn L k) ∧
    P (colourEdges L k 0) (colourFaces L k 0) (holonomyDefectFn L k) ∧
    P (colourFaces L k 0) (colourFaces L k 0) (halfFaceTraceFn L k) ∧
    P (colourEdges L k 0) (colourEdges L k 0) (curvatureFn L k) ∧
    P (colourEdges L k 0) (colourEdges L k 0) (edgeOperatorFn L k) ∧
    P (colourVertices L k 0) (colourVertices L k 0) (vertexOperatorFn L k) ∧
    P (colourEdges L k 0) (colourEdges L k k) (edgeSmoothingFn L k) ∧
    P (colourVertices L k 0) (colourVertices L k k) (vertexSmoothingFn L k)
def edgeFormOf (L k : ℕ) (a : (colourEdges L k 0).UnitQuot → ℂ) :
    PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2 :=
  Tower.ofPauliCoeffs (liftQuotFn (colourEdges L k 0) a)
def faceFunctionOf (L k : ℕ) (a : (colourFaces L k 0).UnitQuot → ℂ) :
    FullSpace.Face L k 0 → Matrices.ComplexMatrix2 :=
  Tower.ofPauliCoeffs (liftQuotFn (colourFaces L k 0) a)
structure PointProperties (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : Prop where
  amplitude_eq : responseAmplitude L k q μ = responseOnAxis L k q μ
  amplitude_bddAbove : BddAbove (range fun b =>
    Matrices.ComplexMatrix2.operatorNorm (edgeFormOf L k (responseAmplitude L k q μ) b))
  curvature_bddAbove : BddAbove (range fun P =>
    Matrices.ComplexMatrix2.operatorNorm (faceFunctionOf L k (responseCurvature L k q μ) P))
  le_bound : ∀ C : ℝ, ResponseBound C →
    supOfOperatorNorms (edgeFormOf L k (responseAmplitude L k q μ)) +
        supOfOperatorNorms (faceFunctionOf L k (responseCurvature L k q μ)) ≤ C
structure JetWellDefined (L k : ℕ) (μPos μNeg : Fin 4) (I I' : PeriodicData)
    (T : ((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop where
  symbol_summable : SymbolSummableOn I I' (coeffZero (Tower.remainderIndex L k) I I' T) univ
  triple_unique : ∀ p, ResponseSymbolSummableAt L k p →
    ActionTripleUnique (Tower.remainderIndex L k) I I' T p (axisField L k p μPos)
      (axisField L k (-p) μNeg)
  isJet : ∀ p, ResponseSymbolSummableAt L k p →
    JetQuad.IsJet (jetWidth p) p (axisJet L k T p μPos μNeg)
def productOver (O : Set (Fin 4 → ℂ)) : Set (Coordinates.ComplexCoordinates (4 + 4)) :=
  {z | sndMomentum z ∈ O}
structure ComponentsHolomorphicOn (L k : ℕ) (μPos μNeg : Fin 4) (O : Set (Fin 4 → ℂ))
    (I I' : PeriodicData) (T : ((Tower.remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) :
    Prop where
  holo_f00 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
      linearMapEntry ((axisJet L k T (sndMomentum z) μPos μNeg).f00 (fstMomentum z)) c' c
  holo_f10 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
      linearMapEntry ((axisJet L k T (sndMomentum z) μPos μNeg).f10 (fstMomentum z)) c' c
  holo_f01 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
      linearMapEntry ((axisJet L k T (sndMomentum z) μPos μNeg).f01 (fstMomentum z)) c' c
  holo_f11 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
      linearMapEntry ((axisJet L k T (sndMomentum z) μPos μNeg).f11 (fstMomentum z)) c' c
structure NeighbourhoodProperties (L k : ℕ) (μPos μNeg : Fin 4) (O : Set (Fin 4 → ℂ)) : Prop where
  response_summable : ∀ p ∈ O, ResponseSymbolSummableAt L k p
  amplitude_pos : HolomorphicOnEntrywise (n := 4) quotFnEntries O
    fun p => axisAmplitude L k p μPos
  amplitude_neg : HolomorphicOnEntrywise (n := 4) quotFnEntries O
    fun p => axisAmplitude L k (-p) μNeg
  curvature_pos : HolomorphicOnEntrywise (n := 4) quotFnEntries O
    fun p => axisCurvature L k p μPos
  curvature_neg : HolomorphicOnEntrywise (n := 4) quotFnEntries O
    fun p => axisCurvature L k (-p) μNeg
  components : ForAllEight L k (ComponentsHolomorphicOn L k μPos μNeg O)
structure HeightProperties (L k : ℕ) : Prop where
  on_polydisc : ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPos μNeg : Fin 4,
    PointProperties L k p μPos ∧ PointProperties L k (-p) μNeg
  coboundary_symbol_summable : SymbolSummableOn (colourEdges L k 0) (colourFaces L k 0)
    (FullSpace.scaledEdgeCoboundaryKernel L k 0) univ
  jets_wellDefined : ∀ μPos μNeg : Fin 4, ForAllEight L k (JetWellDefined L k μPos μNeg)
  exists_nhds : ∀ μPos μNeg : Fin 4,
    ExistsOpenNear IsOpen (momentumPolydisc stripHalfWidth) (NeighbourhoodProperties L k μPos μNeg)
def BackgroundPropertiesHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → HeightProperties L k
end YangMills.Construction.Tower.FullSpace.BackgroundProperties
end
