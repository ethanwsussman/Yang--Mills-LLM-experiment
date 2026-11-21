import YangMills.Construction.RunningCouplingSlope.CellCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.EvaluationsOfKernelsOnASide
import YangMills.Construction.Towers.HessianOfTheWilsonAction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.LocalKernels.Periodisation (periodSide)
structure FreeOperatorsPeriodize (L n k : ℕ) : Prop where
  D : ReadsKernel (I := colourVertices L k 0) (I' := colourEdges L k 0) (colouredVertexProj L n k 0)
    (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).D
    (rescaledOperators L n k (trivialField L n k 0)).D
  Dt : ReadsKernel (I := colourEdges L k 0) (I' := colourVertices L k 0) (colouredEdgeProj L n k 0)
    (colouredVertexProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Dt
    (rescaledOperators L n k (trivialField L n k 0)).Dt
  Q : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k k) (colouredEdgeProj L n k 0)
    (colouredEdgeProj L n k k) (periodSide L n) (trivialRescaledOperators L k).Q
    (rescaledOperators L n k (trivialField L n k 0)).Q
  Qt : ReadsKernel (I := colourEdges L k k) (I' := colourEdges L k 0) (colouredEdgeProj L n k k)
    (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Qt
    (rescaledOperators L n k (trivialField L n k 0)).Qt
  R : ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k k) (colouredVertexProj L n k 0)
    (colouredVertexProj L n k k) (periodSide L n) (trivialRescaledOperators L k).R
    (rescaledOperators L n k (trivialField L n k 0)).R
  Rt : ReadsKernel (I := colourVertices L k k) (I' := colourVertices L k 0) (colouredVertexProj L n k k)
    (colouredVertexProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Rt
    (rescaledOperators L n k (trivialField L n k 0)).Rt
  coboundary : ReadsKernel (I := colourEdges L k 0) (I' := colourFaces L k 0) (colouredEdgeProj L n k 0)
    (colouredFaceProj L n k 0) (periodSide L n) (Tower.FullSpace.scaledEdgeCoboundaryKernel L k 0)
    (Tower.scaledEdgeCoboundaryKernel L n k 0)
  Xi : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k 0) (colouredEdgeProj L n k 0)
    (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Xi
    (rescaledOperators L n k (trivialField L n k 0)).Xi
  Y : ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k 0) (colouredVertexProj L n k 0)
    (colouredVertexProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Y
    (rescaledOperators L n k (trivialField L n k 0)).Y
def FreeOperatorsPeriodizeOnTorus : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k → FreeOperatorsPeriodize L n k
end YangMills.Construction.RunningCouplingSlope
end
