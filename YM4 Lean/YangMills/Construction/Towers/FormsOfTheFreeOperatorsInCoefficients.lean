import YangMills.Construction.Towers.NumbersOfThePlaneWavesAtRealPoints
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FreeSymbolCoefficients
open PeriodicOperators
open PlaneWaves
open FreeResolvents
open Coercivity
open RealFrequencyFamily
def edgeColourCoeffs (L k : ℕ) (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3) (m : Fin 4 → ℤ)
    (μ : Fin 4) : ℂ :=
  pauliCoeff a (edgeFourierCoeff L k b μ m)
def vertexColourCoeffs (L k : ℕ) (u : (colourVertices L k 0).UnitQuot → ℂ) (a : Fin 3)
    (m : Fin 4 → ℤ) : ℂ :=
  pauliCoeff a (vertexFourierCoeff L k u m)
abbrev edgeInner (L k : ℕ) (f g : (colourEdges L k 0).UnitQuot → ℂ) : ℂ :=
  wInner ((colourEdges L k 0).quotWeight 1) f g
abbrev vertexInner (L k : ℕ) (f g : (colourVertices L k 0).UnitQuot → ℂ) : ℂ :=
  wInner ((colourVertices L k 0).quotWeight 1) f g
structure SymbolFormsAt (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  K_selfAdjoint : ∀ f g, edgeInner L k
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ f) g =
    edgeInner L k f
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ g)
  Delta_selfAdjoint : ∀ f g, vertexInner L k
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ f) g =
    vertexInner L k f
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ g)
  Xi_selfAdjoint : ∀ f g, edgeInner L k
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ f) g =
    edgeInner L k f
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ g)
  Y_selfAdjoint : ∀ f g, vertexInner L k
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Y κ f) g =
    vertexInner L k f
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Y κ g)
  edge_norm_sq : ∀ b, edgeInner L k b b =
    ((∑ a, ∑ m ∈ freqBox L k, bondNormSq (edgeColourCoeffs L k b a) m : ℝ) : ℂ)
  vertex_norm_sq : ∀ u, vertexInner L k u u =
    ((∑ a, ∑ m ∈ freqBox L k, ‖vertexColourCoeffs L k u a m‖ ^ 2 : ℝ) : ℂ)
  edge_K : ∀ b, edgeInner L k b
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ b) =
    ((∑ a, bondDirichlet (freqBox L k) (symbolSquares L k κ) (edgeColourCoeffs L k b a) : ℝ) : ℂ)
  vertex_Delta : ∀ u, vertexInner L k u
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ u) =
    ((∑ a, siteDirichlet (freqBox L k) (symbolSquares L k κ) (vertexColourCoeffs L k u a) : ℝ) : ℂ)
  edge_Xi : ∀ b, edgeInner L k b
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ b) =
    ((∑ a, bondQuadraticForm (freqBox L k) (symbolSquares L k κ) (symbols L k κ)
      (vertexWeights L k κ) (edgeWeights L k κ) (edgeColourCoeffs L k b a) : ℝ) : ℂ)
  vertex_Y : ∀ u, vertexInner L k u
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Y κ u) =
    ((∑ a, siteQuadraticForm (freqBox L k) (symbolSquares L k κ) (vertexWeights L k κ)
      (vertexColourCoeffs L k u a) : ℝ) : ℂ)
def FreeSymbolForms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ ∈ realDualPoints, SymbolFormsAt L k κ
end FreeSymbolCoefficients
end Tower
end YangMills.Construction
end
