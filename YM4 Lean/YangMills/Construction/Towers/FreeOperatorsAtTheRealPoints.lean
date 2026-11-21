import YangMills.Construction.Towers.CoercivityOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators
open FreeResolvents
def FreeSymbolsAtRealPoints : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ κ ∈ realDualPoints,
    LoewnerLE (scalarQuotHom (colourEdges L k 0) 0)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ) ∧
    LoewnerLE (scalarQuotHom (colourVertices L k 0) 0)
      (symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ) ∧
    IsAdjointQuotHom
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ)
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ) ∧
    IsAdjointQuotHom
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ)
      (symbolHom (colourVertices L k k) (colourVertices L k 0)
        (trivialRescaledOperators L k).Rt κ) ∧
    quotHomAdjoint
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ) =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ ∧
    quotHomAdjoint
        (symbolHom (colourVertices L k 0) (colourVertices L k k)
          (trivialRescaledOperators L k).R κ) =
      symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ
end YangMills.Construction.Tower
end
