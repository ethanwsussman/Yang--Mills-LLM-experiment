import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseCoefficientFormula
open PeriodicOperators (colourEdges)
open ResponseProperties (InFundamentalStrip ResponseModeEquations)
open FreeStrip (halfSupRate)
def Claim : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p →
      ∀ ε : (colourEdges L k k).UnitQuot → ℂ, ResponseModeEquations L k p ε
end YangMills.Construction.Tower.ResponseCoefficientFormula
end
