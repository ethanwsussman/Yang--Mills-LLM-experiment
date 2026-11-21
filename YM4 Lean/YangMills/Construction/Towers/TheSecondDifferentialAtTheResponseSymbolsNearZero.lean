import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseSecondVariation
open PeriodicOperators (imStrip)
open Tower.FullSpace (IsJointInvertibilityWidth axisPauliElement freePolarizationEntry responseSymbol
  secondVariationSymbol)
open Tower.ResponseProperties (euclidNorm)
def NearZeroCubicBound : Prop :=
  ∀ δ₀ ∈ Tower.FreeStrip.halfSupRate, ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, IsJointInvertibilityWidth L k hL δ →
      ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), N ⊆ imStrip δ ∩ imStrip (2 * δ₀) ∧
        ∀ p ∈ N, ∀ μ ν : Fin 4,
          ‖secondVariationSymbol L k hL p (responseSymbol L k hL p (axisPauliElement μ 2))
                (responseSymbol L k hL (-p) (axisPauliElement ν 2)) -
              freePolarizationEntry L k hL μ ν p‖ ≤ C * euclidNorm p ^ 3
end YangMills.Construction.Tower.ResponseSecondVariation
end
