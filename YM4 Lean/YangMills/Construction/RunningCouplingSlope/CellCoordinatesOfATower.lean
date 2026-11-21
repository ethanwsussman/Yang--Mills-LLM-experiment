import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import YangMills.Construction.RunningCouplingSlope.LocalMatrixOfABoundedSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
def colouredVertexProj (L n k m : ℕ) (i : (colourVertices L k m).Carrier) :
    Fin 3 × Vertex L n k m :=
  (i.1, FullSpace.projVertex L n k m i.2)
def colouredEdgeProj (L n k m : ℕ) (i : (colourEdges L k m).Carrier) :
    Fin 3 × Tower.PositiveEdge L n k m :=
  (i.1, LocalKernels.projPositiveEdge L n k m i.2)
def colouredFaceProj (L n k m : ℕ) (i : (colourFaces L k m).Carrier) :
    Fin 3 × Face L n k m :=
  (i.1, FullSpace.projFace L n k m i.2)
def CellQuotientsOfTower : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    IsCellQuotient L n k (colourVertices L k 0) (colouredVertexProj L n k 0) colouredVertexCell ∧
    IsCellQuotient L n k (colourEdges L k 0) (colouredEdgeProj L n k 0) colouredEdgeCell ∧
    IsCellQuotient L n k (colourFaces L k 0) (colouredFaceProj L n k 0)
      colouredFaceCell ∧
    IsCellQuotient L n k (colourVertices L k k) (colouredVertexProj L n k k) vertexCell ∧
    IsCellQuotient L n k (colourEdges L k k) (colouredEdgeProj L n k k) edgeCell
end YangMills.Construction.RunningCouplingSlope
end
