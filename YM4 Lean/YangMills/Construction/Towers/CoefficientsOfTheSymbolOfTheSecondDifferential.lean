import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SymbolCoefficients
open PeriodicOperators (imStrip)
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
def HolomorphicBoundedOnStrip (L k : ℕ) (hL : 0 < L) (δPlus : ℝ)
    (a : (fieldPeriodicData L k hL).UnitQuot → (fieldPeriodicData L k hL).UnitQuot →
      (Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ c c' : (fieldPeriodicData L k hL).UnitQuot,
    IsHolomorphicScalarIn (interior (imStrip δPlus)) (a c c') ∧
      ∃ M : ℝ, ∀ p ∈ imStrip δPlus, ‖a c c' p‖ ≤ M
def RepresentsSymbolOn (L k : ℕ) (hL : 0 < L) (δ : ℝ)
    (a : (fieldPeriodicData L k hL).UnitQuot → (fieldPeriodicData L k hL).UnitQuot →
      (Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ p ∈ imStrip δ, ∀ εPlus εMinus : (fieldPeriodicData L k hL).UnitQuot → ℂ,
    secondVariationSymbol L k hL p εPlus εMinus =
      ∑ᶠ c, ∑ᶠ c', a c c' p * εPlus c * εMinus c'
def SymbolCoefficientsExist : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ δ : ℝ, IsJointInvertibilityWidth L k hL δ →
      ∃ δPlus : ℝ, δ < δPlus ∧ IsJointInvertibilityWidth L k hL δPlus ∧
        ∃ a : (fieldPeriodicData L k hL).UnitQuot → (fieldPeriodicData L k hL).UnitQuot →
            (Fin 4 → ℂ) → ℂ,
          HolomorphicBoundedOnStrip L k hL δPlus a ∧ RepresentsSymbolOn L k hL δ a
end YangMills.Construction.Tower.FullSpace.SymbolCoefficients
end
