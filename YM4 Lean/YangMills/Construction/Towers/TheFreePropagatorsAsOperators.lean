import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.PeriodicOperators
def edgeResolvent (L k : ℕ) :
    KernelMatrix (colourEdges L k 0).Carrier (colourEdges L k 0).Carrier :=
  periodicInverse (colourEdges L k 0) (edgeOperatorAddOne L k)
def vertexResolvent (L k : ℕ) :
    KernelMatrix (colourVertices L k 0).Carrier (colourVertices L k 0).Carrier :=
  periodicInverse (colourVertices L k 0) (vertexOperatorAddOne L k)
def edgeResolventSqrt (L k : ℕ) :
    KernelMatrix (colourEdges L k 0).Carrier (colourEdges L k 0).Carrier :=
  matFunKernel (colourEdges L k 0) (colourEdges L k 0) (edgePowMatrix L k (-(1 / 2)))
def vertexResolventSqrt (L k : ℕ) :
    KernelMatrix (colourVertices L k 0).Carrier (colourVertices L k 0).Carrier :=
  matFunKernel (colourVertices L k 0) (colourVertices L k 0) (vertexPowMatrix L k (-(1 / 2)))
def edgeResolventInvSqrt (L k : ℕ) :
    KernelMatrix (colourEdges L k 0).Carrier (colourEdges L k 0).Carrier :=
  matFunKernel (colourEdges L k 0) (colourEdges L k 0) (edgePowMatrix L k (1 / 2))
def vertexResolventInvSqrt (L k : ℕ) :
    KernelMatrix (colourVertices L k 0).Carrier (colourVertices L k 0).Carrier :=
  matFunKernel (colourVertices L k 0) (colourVertices L k 0) (vertexPowMatrix L k (1 / 2))
def edgeResolventSqrtSymbol (L k : ℕ) (κ : Fin 4 → ℂ) :
    QuotHom (colourEdges L k 0) (colourEdges L k 0) :=
  symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolventSqrt L k) κ
end YangMills.Construction.Tower.FreeResolvents
end
