import YangMills.Construction.Towers.PartsOfTheHessianOfTheWilsonAction
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open PeriodicOperators
open BackgroundFieldResponse (responseKernel)
open Classical in
def stripHalfWidth : ℝ := FreeStrip.halfSupRate.getOrElse 0
theorem stripHalfWidth_mem (hdom : FreeStrip.halfSupRate.Dom) :
    stripHalfWidth ∈ FreeStrip.halfSupRate := by
  classical
  rw [stripHalfWidth, Part.getOrElse_of_dom _ hdom]
  exact Part.get_mem hdom
def momentumPolydisc (δ : ℝ) : Set (Fin 4 → ℂ) := {p | ∀ μ, ‖p μ‖ ≤ δ}
def massWidth (z : ℝ) : ℝ := min stripHalfWidth (1 / 5 * Real.sqrt z)
def responseAmplitude (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (colourEdges L k 0).UnitQuot → ℂ :=
  waveAmplitude (colourEdges L k 0) q
    (applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)))
def responseCurvature (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) :
    (colourFaces L k 0).UnitQuot → ℂ :=
  waveAmplitude (colourFaces L k 0) q
    ((edgePauliCoordinates L k 0).mapOnCoeffs (Tower.vertexCoordinate (Face L k 0)) scaledEdgeCoboundary
      (blochWave (colourEdges L k 0) q (responseAmplitude L k q μ)))
def scaledResponseField (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : (remainderIndex L k).UnitQuot → ℂ :=
  ((finestMesh L k : ℝ) : ℂ) • responseAmplitude L k q μ
def jetAlongResponse {I I' : PeriodicData} (L k : ℕ)
    (T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (p : Fin 4 → ℂ)
    (μ₁ μ₂ : Fin 4) : JetQuad I I' :=
  jetAlong (remainderIndex L k) I I' T p (scaledResponseField L k p μ₁)
    (scaledResponseField L k (-p) μ₂)
def gaugeFieldOfForm (L k : ℕ) (f : (remainderIndex L k).Carrier → ℂ) :
    Edge L k 0 → Matrices.ComplexMatrix2 :=
  expForm ((edgePauliCoordinates L k 0).ofCoeffs f)
def covDerivJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourVertices L k 0) (colourEdges L k 0) :=
  jetAlongResponse L k (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).D) p μ₁ μ₂
def holonomyDefectJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourEdges L k 0) (colourFaces L k 0) :=
  jetAlongResponse L k (fun f => holonomyDefectKernel L k (gaugeFieldOfForm L k f)) p μ₁ μ₂
def halfFaceTraceJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourFaces L k 0) (colourFaces L k 0) :=
  jetAlongResponse L k (fun f => halfFaceTraceKernel L k (gaugeFieldOfForm L k f)) p μ₁ μ₂
def curvatureJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  jetAlongResponse L k (fun f => curvatureKernel (gaugeFieldOfForm L k f)) p μ₁ μ₂
def edgeOperatorJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  jetAlongResponse L k (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).K) p μ₁ μ₂
def vertexOperatorJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourVertices L k 0) (colourVertices L k 0) :=
  jetAlongResponse L k (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Delta) p μ₁ μ₂
def edgeSmoothingJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourEdges L k 0) (colourEdges L k k) :=
  jetAlongResponse L k (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Q) p μ₁ μ₂
def vertexSmoothingJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourVertices L k 0) (colourVertices L k k) :=
  jetAlongResponse L k (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).R) p μ₁ μ₂
def covDerivDefectJet (L k : ℕ) (p : Fin 4 → ℂ) (μ₁ μ₂ : Fin 4) :
    JetQuad (colourVertices L k 0) (colourEdges L k 0) :=
  (covDerivJet L k p μ₁ μ₂).add
    (JetQuad.smul (-1)
      (JetQuad.ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0)))
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
