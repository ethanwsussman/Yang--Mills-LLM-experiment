import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseProperties
open PeriodicOperators (colourEdges)
open FreeStrip (halfSupRate)
def responseConstant : ℝ := Classical.epsilon ResponseBound
def AllProperties : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ResponseRelations L k) ∧
  (∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p →
      ∀ ε : (colourEdges L k k).UnitQuot → ℂ, ResponseModeEquations L k p ε) ∧
  ResponseBound responseConstant ∧
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    SmallMomentumBehaviour δ₀ L k
end YangMills.Construction.Tower.ResponseProperties
end
