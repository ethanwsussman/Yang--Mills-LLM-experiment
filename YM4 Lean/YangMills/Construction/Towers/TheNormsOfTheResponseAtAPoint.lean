import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseNormBounds
open PeriodicOperators (colourEdges wNorm)
open PlaneWaveCalculus (topEdgeComponent topVertexElement)
open ResponseProperties (InFundamentalStrip smoothedDivergence responseSymbolForm defectSymbol)
open FreeStrip (halfSupRate)
def BoundsNorms (C : ℝ) : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p → ∀ ε : (colourEdges L k k).UnitQuot → ℂ,
      wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε) ≤
          C * pauliFamilyNorm (topEdgeComponent L k ε) ∧
        pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) ≤
          C * pauliFamilyNorm (topEdgeComponent L k ε) ∧
        pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)) ≤
          C * pauliFamilyNorm (topEdgeComponent L k ε)
def Claim : Prop := ∃ C : ℝ, BoundsNorms C
end YangMills.Construction.Tower.ResponseNormBounds
end
