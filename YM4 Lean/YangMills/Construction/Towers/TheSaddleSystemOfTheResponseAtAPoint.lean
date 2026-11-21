import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseSaddleSystem
open PeriodicOperators (colourEdges symbolHom)
open FreeResolvents (trivialRescaledOperators)
open ResponseProperties (InFundamentalStrip responseSymbolForm defectSymbol)
open FreeStrip (halfSupRate)
def Claim : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p → ∀ ε : (colourEdges L k k).UnitQuot → ℂ,
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p
          (responseSymbolForm L k p ε) =
        symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p
          (defectSymbol L k p ε) ∧
      symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q p
          (responseSymbolForm L k p ε) = ε
end YangMills.Construction.Tower.ResponseSaddleSystem
end
