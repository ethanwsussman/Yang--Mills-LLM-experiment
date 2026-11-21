import YangMills.Construction.ResponseInTheExpansion.GaussianSymbolOverALattice
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.LatticeFourier
def cutPairSymbolTerm (χ : (Fin 4 → ℝ) → ℝ) (N : ℕ) (z : Fin 4 → ℝ) (a b : Fin 4)
    (k : Fin 4 → ℤ) : ℂ :=
  ((χ (fun i => circleMomentum N (k i)) * (circleMomentum N (k a) * circleMomentum N (k b)) /
      ∑ i, circleMomentum N (k i) ^ 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ))
def cutPairSymbolLatticeStatement : Prop :=
  ∀ χ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ χ → (∀ᶠ p in nhds 0, χ p = 1) →
    (∀ p, 1 ≤ ∑ i, p i ^ 2 → χ p = 0) →
    ∃ C : ℝ, ∀ (N : ℕ) (x : Fin 4 → ℝ) (a b : Fin 4), 8 ≤ N → 1 ≤ ∑ i, x i ^ 2 →
      ∑ i, x i ^ 2 ≤ ((N : ℝ) / 8) ^ 2 →
      Summable (cutPairSymbolTerm χ N x a b) ∧
      ‖((N : ℂ) ^ 4)⁻¹ * ∑' k, cutPairSymbolTerm χ N x a b k - (greenHessian x a b : ℂ)‖ ≤
        C * ((∑ i, x i ^ 2) ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)))
end YangMills.Construction.LatticeFourier
