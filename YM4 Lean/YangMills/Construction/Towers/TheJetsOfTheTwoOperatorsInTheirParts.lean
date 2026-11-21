import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetDecomposition
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
def vertexCoboundaryJet (L k : ℕ) : JetQuad (colourVertices L k 0) (colourEdges L k 0) :=
  ofKernel (colourVertices L k 0) (colourEdges L k 0) (scaledVertexCoboundaryKernel L k 0)
def edgeCoboundaryJet (L k : ℕ) : JetQuad (colourEdges L k 0) (colourFaces L k 0) :=
  ofKernel (colourEdges L k 0) (colourFaces L k 0)
    (scaledEdgeCoboundaryKernel L k 0)
def vertexCoboundaryAddDefect (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    JetQuad (colourVertices L k 0) (colourEdges L k 0) :=
  (vertexCoboundaryJet L k).add (covDerivDefectJet L k p μPlus μMinus)
def edgeCoboundaryAddDefect (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    JetQuad (colourEdges L k 0) (colourFaces L k 0) :=
  (edgeCoboundaryJet L k).add (holonomyDefectJet L k p μPlus μMinus)
structure OperatorJetsDecompose (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) : Prop where
  covDeriv : EqAsJet stripHalfWidth p (covDerivJet L k p μPlus μMinus)
    (vertexCoboundaryAddDefect L k p μPlus μMinus)
  edge_operator : EqAsJet stripHalfWidth p (edgeOperatorJet L k p μPlus μMinus)
    (((mul p (transposeAt p (edgeCoboundaryAddDefect L k p μPlus μMinus))
        (mul p (halfFaceTraceJet L k p μPlus μMinus)
          (edgeCoboundaryAddDefect L k p μPlus μMinus))).add
      (curvatureJet L k p μPlus μMinus)).add
      (mul p (vertexCoboundaryAddDefect L k p μPlus μMinus)
        (transposeAt p (vertexCoboundaryAddDefect L k p μPlus μMinus))))
  vertex_operator : EqAsJet stripHalfWidth p (vertexOperatorJet L k p μPlus μMinus)
    (mul p (transposeAt p (vertexCoboundaryAddDefect L k p μPlus μMinus))
      (vertexCoboundaryAddDefect L k p μPlus μMinus))
  free_edge_operator : EqAsJet stripHalfWidth p
    (ofKernel (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K)
    ((mul p (transposeAt p (edgeCoboundaryJet L k)) (edgeCoboundaryJet L k)).add
      (mul p (vertexCoboundaryJet L k) (transposeAt p (vertexCoboundaryJet L k))))
  free_vertex_operator : EqAsJet stripHalfWidth p
    (ofKernel (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta)
    (mul p (transposeAt p (vertexCoboundaryJet L k)) (vertexCoboundaryJet L k))
def DecompositionHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      OperatorJetsDecompose L k p μPlus μMinus
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetDecomposition
end
