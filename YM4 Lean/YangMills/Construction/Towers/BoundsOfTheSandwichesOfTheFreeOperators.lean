import YangMills.Construction.Towers.TheFreePropagatorsAsOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.SandwichBounds
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.Tower.FreeResolvents
def sandwichConstant : ℝ := 101 + 200 * Real.exp 2
def SandwichNormsBounded {I : PeriodicData} (N X K : QuotHom I I) : Prop :=
  quotHomNorm (N.comp (X.comp N)) ≤ ENNReal.ofReal sandwichConstant ∧
    quotHomNorm (N.comp (K.comp N)) ≤ ENNReal.ofReal sandwichConstant ∧
    quotHomNorm (N.comp N) ≤ ENNReal.ofReal sandwichConstant
def FreeSandwichBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ ∈ openStripInterior (1 / 8),
    SandwichNormsBounded
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolventSqrt L k) κ)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ) ∧
    SandwichNormsBounded
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolventSqrt L k) κ)
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Y κ)
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ)
end YangMills.Construction.Tower.SandwichBounds
end
