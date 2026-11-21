import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import YangMills.Construction.Towers.TheFreePropagatorsAsOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace DiagonalSymbolBounds
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open FreeResolvents
structure SymbolBoundsAt (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  edgeSqrt_le : quotHomNorm (edgeResolventSqrtSymbol L k κ) ≤ ENNReal.ofReal 10
  vertexSqrt_le : quotHomNorm (symbolHom (colourVertices L k 0) (colourVertices L k 0)
    (vertexResolventSqrt L k) κ) ≤ ENNReal.ofReal 10
  coboundary_comp_edgeSqrt_le : quotHomNorm ((symbolHom (colourEdges L k 0) (colourFaces L k 0)
    (FullSpace.scaledEdgeCoboundaryKernel L k 0) κ).comp (edgeResolventSqrtSymbol L k κ)) ≤
      ENNReal.ofReal 10
  coboundaryTranspose_comp_edgeSqrt_le : quotHomNorm ((symbolHom (colourEdges L k 0) (colourVertices L k 0)
    (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0)) κ).comp (edgeResolventSqrtSymbol L k κ)) ≤
      ENNReal.ofReal 10
  edgeSqrt_comp_coboundary_le : quotHomNorm ((edgeResolventSqrtSymbol L k κ).comp
    (symbolHom (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.scaledVertexCoboundaryKernel L k 0) κ)) ≤ ENNReal.ofReal 10
  edgeSqrt_comp_coboundaryTranspose_le : quotHomNorm ((edgeResolventSqrtSymbol L k κ).comp
    (symbolHom (colourFaces L k 0) (colourEdges L k 0)
      (kernelTranspose (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0)) κ)) ≤ ENNReal.ofReal 10
  coboundary_comp_vertexSqrt_le : quotHomNorm ((symbolHom (colourVertices L k 0) (colourEdges L k 0)
    (FullSpace.scaledVertexCoboundaryKernel L k 0) κ).comp
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolventSqrt L k) κ)) ≤
      ENNReal.ofReal 10
  vertexSqrt_comp_coboundaryTranspose_le : quotHomNorm ((symbolHom (colourVertices L k 0) (colourVertices L k 0)
    (vertexResolventSqrt L k) κ).comp
      (symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
          (FullSpace.scaledVertexCoboundaryKernel L k 0)) κ)) ≤ ENNReal.ofReal 10
def DiagonalSymbolBoundsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ ∈ openStripInterior (1 / 8), SymbolBoundsAt L k κ
end DiagonalSymbolBounds
end Tower
end YangMills.Construction
end
