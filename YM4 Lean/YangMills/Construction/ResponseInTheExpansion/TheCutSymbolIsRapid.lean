import Mathlib
set_option autoImplicit false
open scoped SchwartzMap ContDiff
namespace YangMills.Construction.LatticeFourier
def cutoffSymbolSchwartzStatement : Prop :=
  ∀ χ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ χ → (∀ᶠ p in nhds 0, χ p = 1) →
    (∀ p, 1 ≤ ∑ i, p i ^ 2 → χ p = 0) → ∀ a b : Fin 4, ∃ f : 𝓢(Fin 4 → ℝ, ℂ), ∀ p,
      f p = (((χ p - Real.exp (-∑ i, p i ^ 2)) * (p a * p b) / ∑ i, p i ^ 2 : ℝ) : ℂ)
end YangMills.Construction.LatticeFourier
