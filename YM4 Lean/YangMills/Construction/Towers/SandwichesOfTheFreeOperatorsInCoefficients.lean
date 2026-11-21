import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficients
import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import YangMills.Construction.Towers.TheFreePropagatorsAsOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FreeSandwiches
open PeriodicOperators
open PlaneWaves
open FreeResolvents
open Coercivity
open RealFrequencyFamily
open PlaneWaveCalculus (topEdgeComponent topVertexElement)
def topEdgeCoeff (L k : ℕ) (z : (colourEdges L k k).UnitQuot → ℂ) (a : Fin 3) (μ : Fin 4) : ℂ :=
  pauliCoeff a (topEdgeComponent L k z μ)
def topVertexCoeff (L k : ℕ) (g : (colourVertices L k k).UnitQuot → ℂ) (a : Fin 3) : ℂ :=
  pauliCoeff a (topVertexElement L k g)
abbrev topEdgeInner (L k : ℕ) (f g : (colourEdges L k k).UnitQuot → ℂ) : ℂ :=
  wInner ((colourEdges L k k).quotWeight 1) f g
abbrev topVertexInner (L k : ℕ) (f g : (colourVertices L k k).UnitQuot → ℂ) : ℂ :=
  wInner ((colourVertices L k k).quotWeight 1) f g
def edgeSandwich (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (colourEdges L k k) (colourEdges L k k) :=
  (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ).comp
    ((symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) κ).comp
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ))
def vertexSandwich (L k : ℕ) (κ : Fin 4 → ℂ) :
    QuotHom (colourVertices L k k) (colourVertices L k k) :=
  (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ).comp
    ((symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) κ).comp
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ))
structure SandwichFactsAt (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  edge_adjoint : ∀ f g, topEdgeInner L k g
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ f) =
    FreeSymbolCoefficients.edgeInner L k
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ g) f
  vertex_adjoint : ∀ f g, topVertexInner L k g
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ f) =
    FreeSymbolCoefficients.vertexInner L k
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ g) f
  edge_hermitian : ∀ z w, topEdgeInner L k (edgeSandwich L k κ z) w =
    topEdgeInner L k z (edgeSandwich L k κ w)
  vertex_hermitian : ∀ g h, topVertexInner L k (vertexSandwich L k κ g) h =
    topVertexInner L k g (vertexSandwich L k κ h)
  edge_norm : ∀ z, topEdgeInner L k z z =
    ((∑ a, ∑ μ, ‖topEdgeCoeff L k z a μ‖ ^ 2 : ℝ) : ℂ)
  vertex_norm : ∀ g, topVertexInner L k g g =
    ((∑ a, ‖topVertexCoeff L k g a‖ ^ 2 : ℝ) : ℂ)
  edge_form : ∀ z, topEdgeInner L k z (edgeSandwich L k κ z) =
    ((∑ a, ∑ μ, bondResolventWeight (freqBox L k) (symbolSquares L k κ) (edgeWeights L k κ) μ *
      ‖topEdgeCoeff L k z a μ‖ ^ 2 : ℝ) : ℂ)
  vertex_form : ∀ g, topVertexInner L k g (vertexSandwich L k κ g) =
    ((∑ a, siteResolventWeight (freqBox L k) (symbolSquares L k κ) (vertexWeights L k κ) *
      ‖topVertexCoeff L k g a‖ ^ 2 : ℝ) : ℂ)
def SandwichFacts : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ ∈ realDualPoints, SandwichFactsAt L k κ
end FreeSandwiches
end Tower
end YangMills.Construction
end
