import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.FreeResolvents (trivialRescaledOperators)
def FreeXSymbolNonneg : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ κ ∈ realDualPoints,
    symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ -
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ).comp
          (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ) ∧
    ∀ b : (colourEdges L k 0).UnitQuot → ℂ,
      0 ≤ (wInner ((colourEdges L k 0).quotWeight 1) b
        (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b)).re
end YangMills.Construction.RunningCouplingSlope
end
