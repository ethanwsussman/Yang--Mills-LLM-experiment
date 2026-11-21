import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.StepEntryBounds
open PeriodicOperators.Tempered.OneStep
def CongruentMod (L : ℕ) (m m' : Fin 4 → ℤ) : Prop := ∀ ν, (L : ℤ) ∣ m ν - m' ν
def kroneckerEntry (ρ μ : Fin 4) : ℂ := if ρ = μ then 1 else 0
structure HoldsAt (δ₀ : ℝ) (L i : ℕ) : Prop where
  eq_of_congr : ∀ m m' : Fin 4 → ℤ, CongruentMod L m m' → ∀ κ ρ μ,
    stepEntry L i m κ ρ μ = stepEntry L i m' κ ρ μ
  holomorphic : ∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ PeriodicOperators.imStrip (2 * δ₀) ⊆ O ∧
    ∀ m' ρ μ, Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O
      fun κ _ => stepEntry L i m' κ ρ μ
  bounded : ∃ C : ℝ, ∀ m' ρ μ, ∀ κ ∈ PeriodicOperators.imStrip (2 * δ₀),
    ‖stepEntry L i m' κ ρ μ‖ ≤ C
  near_zero : ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N,
    p ∈ PeriodicOperators.imStrip (2 * δ₀) → ∀ m' ρ μ,
      (¬ CongruentMod L m' 0 →
          ‖stepEntry L i m' p ρ μ‖ ≤ C * Tower.ResponseProperties.euclidNorm p ^ 2) ∧
        (CongruentMod L m' 0 →
          ‖stepEntry L i m' p ρ μ - kroneckerEntry ρ μ‖ ≤
            C * Tower.ResponseProperties.euclidNorm p)
def Claim : Prop :=
  ∀ δ₀ ∈ Tower.FreeStrip.halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ i : ℕ, HoldsAt δ₀ L i
end YangMills.Construction.Tower.StepEntryBounds
end
