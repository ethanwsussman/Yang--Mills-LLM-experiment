import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperators
import YangMills.Construction.Towers.TheResponseInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseProperties
open YangMills.Construction.PeriodicOperators (KernelMatrix CompSummableAt colourEdges colourVertices
  wNorm idKernel compKernel imStrip symbolHom)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect)
open YangMills.Construction.Tower.PlaneWaveCalculus (edgeCoboundaryT vertexCoboundaryT topEdgeComponent
  topVertexElement integerWave expWave)
open YangMills.Construction.Tower.PlaneWaves (edgeAt edgeWeight forwardSymbol symbolSquare
  edgeFourierCoeff freqBox shiftedFreq)
open YangMills.Construction.Tower.FreeStrip (halfSupRate)
open YangMills.Construction.PeriodicLattice (supOfOperatorNorms)
def CompSummableEverywhere {J J' J'' : Type} (T : J' → J → ℂ) (S : J → J'' → ℂ) : Prop :=
  ∀ i' i'', CompSummableAt T S i' i''
def coboundaryLaplacian (L k : ℕ) : KernelMatrix (colourEdges L k 0).Carrier (colourEdges L k 0).Carrier :=
  compKernel (edgeCoboundaryT L k 0) (FullSpace.scaledEdgeCoboundaryKernel L k 0)
def oneMinusSmoothingSquare (L k : ℕ) :
    KernelMatrix (colourVertices L k 0).Carrier (colourVertices L k 0).Carrier :=
  fun i' i => idKernel (colourVertices L k 0) i' i -
    compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R i' i
def responseDivergenceKernel (L k : ℕ) :
    KernelMatrix (colourEdges L k k).Carrier (colourVertices L k 0).Carrier :=
  compKernel (vertexCoboundaryT L k 0) (responseKernel L k)
structure ResponseRelations (L k : ℕ) : Prop where
  smoothing_comp_summable : CompSummableEverywhere (trivialRescaledOperators L k).Q (responseKernel L k)
  smoothing_comp : compKernel (trivialRescaledOperators L k).Q (responseKernel L k) =
    idKernel (colourEdges L k k)
  laplacian_summable : CompSummableEverywhere (edgeCoboundaryT L k 0)
    (FullSpace.scaledEdgeCoboundaryKernel L k 0)
  laplacian_comp_summable : CompSummableEverywhere (coboundaryLaplacian L k) (responseKernel L k)
  defect_summable : CompSummableEverywhere (trivialRescaledOperators L k).Qt (responseDefect L k)
  laplacian_comp : compKernel (coboundaryLaplacian L k) (responseKernel L k) =
    compKernel (trivialRescaledOperators L k).Qt (responseDefect L k)
  smoothing_square_summable : CompSummableEverywhere (trivialRescaledOperators L k).Rt
    (trivialRescaledOperators L k).R
  divergence_summable : CompSummableEverywhere (vertexCoboundaryT L k 0) (responseKernel L k)
  gauge_summable : CompSummableEverywhere (oneMinusSmoothingSquare L k) (responseDivergenceKernel L k)
  gauge_comp : compKernel (oneMinusSmoothingSquare L k) (responseDivergenceKernel L k) = 0
  defect_divergence_summable : CompSummableEverywhere (vertexCoboundaryT L k k)
    (responseDefect L k)
  defect_divergence : compKernel (vertexCoboundaryT L k k) (responseDefect L k) = 0
def InFundamentalStrip (δ₀ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  p ∈ imStrip (2 * δ₀) ∧ ∀ ρ, |(p ρ).re| ≤ Real.pi
def responseSymbolForm (L k : ℕ) (p : Fin 4 → ℂ) (ε : (colourEdges L k k).UnitQuot → ℂ) :
    (colourEdges L k 0).UnitQuot → ℂ :=
  symbolHom (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) p ε
def defectSymbol (L k : ℕ) (p : Fin 4 → ℂ) (ε : (colourEdges L k k).UnitQuot → ℂ) :
    (colourEdges L k k).UnitQuot → ℂ :=
  symbolHom (colourEdges L k k) (colourEdges L k k) (responseDefect L k) p ε
def smoothedDivergence (L k : ℕ) (p : Fin 4 → ℂ) (ε : (colourEdges L k k).UnitQuot → ℂ) :
    (colourVertices L k k).UnitQuot → ℂ :=
  symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R p
    (symbolHom (colourEdges L k 0) (colourVertices L k 0) (vertexCoboundaryT L k 0) p
      (responseSymbolForm L k p ε))
def ResponseModeEquations (L k : ℕ) (p : Fin 4 → ℂ) (ε : (colourEdges L k k).UnitQuot → ℂ) : Prop :=
  ∀ m ∈ freqBox L k, ∀ μ : Fin 4,
    symbolSquare L k (shiftedFreq p m) • edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m =
      edgeWeight L k (-shiftedFreq p m) μ • topEdgeComponent L k (defectSymbol L k p ε) μ +
        (forwardSymbol L k (shiftedFreq p m) μ * Tower.PlaneWaves.vertexWeight L k (-shiftedFreq p m)) •
          topVertexElement L k (smoothedDivergence L k p ε)
def IsFourierSynthesis (L k : ℕ) (b : (colourEdges L k 0).UnitQuot → ℂ)
    (α : PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ (x : FullSpace.Vertex L k 0) (μ : Fin 4),
    α (edgeAt L k x μ) = ∑ m ∈ freqBox L k, integerWave m x • edgeFourierCoeff L k b μ m
def modulatedForm (L k : ℕ) (p : Fin 4 → ℂ) (α : PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k 0 → Matrices.ComplexMatrix2 :=
  open Classical in
  FullSpace.extendOddly fun e => if he : e.IsPositivelyOriented then expWave p e.initial • α ⟨e, he⟩ else 0
def IsCoboundaryFactor (L k : ℕ) (p : Fin 4 → ℂ)
    (α : PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2)
    (f : FullSpace.Face L k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ P : FullSpace.Face L k 0,
    FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) (modulatedForm L k p α) P =
      expWave p P.corner • f P
def ResponseBound (C : ℝ) : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p → ∀ (ε : (colourEdges L k k).UnitQuot → ℂ)
      (α : PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2)
      (f : FullSpace.Face L k 0 → Matrices.ComplexMatrix2),
      IsFourierSynthesis L k (responseSymbolForm L k p ε) α → IsCoboundaryFactor L k p α f →
      BddAbove (range fun e => Matrices.ComplexMatrix2.operatorNorm (α e)) ∧
      BddAbove (range fun P => Matrices.ComplexMatrix2.operatorNorm (f P)) ∧
      wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε) +
          pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) +
          pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)) +
          supOfOperatorNorms α + supOfOperatorNorms f ≤
        C * pauliFamilyNorm (topEdgeComponent L k ε)
def euclidNorm (y : Fin 4 → ℂ) : ℝ := Real.sqrt (∑ ρ, ‖y ρ‖ ^ 2)
def SmallMomentumBehaviour (δ₀ : ℝ) (L k : ℕ) : Prop :=
  ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N, InFundamentalStrip δ₀ p →
    ∀ ε : (colourEdges L k k).UnitQuot → ℂ,
      (∀ m ∈ freqBox L k, m ≠ 0 →
        pauliFamilyNorm (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) ≤
          C * (euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k ε))) ∧
      pauliFamilyNorm
          (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ 0 - topEdgeComponent L k ε μ) ≤
        C * (euclidNorm p * pauliFamilyNorm (topEdgeComponent L k ε)) ∧
      pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) ≤
        C * (euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L k ε))
end YangMills.Construction.Tower.ResponseProperties
end
