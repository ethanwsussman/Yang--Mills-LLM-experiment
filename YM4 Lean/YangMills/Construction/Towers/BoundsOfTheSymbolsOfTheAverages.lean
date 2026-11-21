import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.SymbolBounds
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open FreeResolvents
def FreeSymbolNormBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ ∈ openStripInterior (1 / 8),
    quotHomNorm (symbolHom (colourEdges L k 0) (colourEdges L k k)
        (trivialRescaledOperators L k).Q κ) ≤
      ENNReal.ofReal (Real.exp 1) ∧
    quotHomNorm (symbolHom (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R κ) ≤
      ENNReal.ofReal (Real.exp 1) ∧
    quotHomNorm (symbolHom (colourEdges L k k) (colourEdges L k 0)
        (trivialRescaledOperators L k).Qt κ) ≤
      ENNReal.ofReal (Real.exp 1) ∧
    quotHomNorm (symbolHom (colourVertices L k k) (colourVertices L k 0)
        (trivialRescaledOperators L k).Rt κ) ≤
      ENNReal.ofReal (Real.exp 1)
end YangMills.Construction.Tower.SymbolBounds
end
