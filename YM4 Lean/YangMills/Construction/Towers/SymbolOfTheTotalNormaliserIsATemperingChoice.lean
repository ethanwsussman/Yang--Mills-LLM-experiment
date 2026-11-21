import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserSymbol
open PeriodicOperators (imStrip)
open PeriodicOperators.Tempered (IsTemperedWitness SymbolArray)
open FullSpace (IsJointInvertibilityWidth axisPauliElement responseSymbol secondVariationSymbol)
def SymbolArrayMatchesAt (L k : ℕ) (hL : 0 < L) (π : SymbolArray) (p : Fin 4 → ℂ) : Prop :=
  ∀ (a a' : Fin 3) (μ ν : Fin 4),
    (if a = a' then π μ ν p else 0) =
      secondVariationSymbol L k hL p (responseSymbol L k hL p (axisPauliElement μ a))
        (responseSymbol L k hL (-p) (axisPauliElement ν a'))
def IsTemperedWitnessClaim : Prop :=
  ∀ δ₀ ∈ FreeStrip.halfSupRate, ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, IsJointInvertibilityWidth L k hL δ →
      ∃ (π : SymbolArray) (e : ℕ → ℝ),
        IsTemperedWitness L (logNormaliserFamily L k) (min δ (2 * δ₀)) π e ∧
          ∀ p ∈ imStrip δ ∩ imStrip (2 * δ₀), SymbolArrayMatchesAt L k hL π p
end YangMills.Construction.Tower.NormaliserSymbol
end
