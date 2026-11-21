import YangMills.Construction.ResponseInTheExpansion.HeatSumOnALine
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
def gaussianSymbolTerm (N : ℕ) (z : Fin 4 → ℝ) (a b : Fin 4) (k : Fin 4 → ℤ) : ℂ :=
  ((Real.exp (-∑ i, circleMomentum N (k i) ^ 2) * (circleMomentum N (k a) * circleMomentum N (k b)) /
      ∑ i, circleMomentum N (k i) ^ 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ))
def greenHessian (z : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ((if a = b then 1 else 0) - 4 * z a * z b / ∑ i, z i ^ 2) /
    (2 * Real.pi ^ 2 * (∑ i, z i ^ 2) ^ 2)
def gaussianSymbolLatticeStatement : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (z : Fin 4 → ℝ) (a b : Fin 4), 8 ≤ N → 1 ≤ ∑ i, z i ^ 2 →
    ∑ i, z i ^ 2 ≤ ((N : ℝ) / 8) ^ 2 →
    Summable (gaussianSymbolTerm N z a b) ∧
    ‖((N : ℂ) ^ 4)⁻¹ * ∑' k, gaussianSymbolTerm N z a b k - (greenHessian z a b : ℂ)‖ ≤
      C * ((∑ i, z i ^ 2) ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)))
end YangMills.Construction.LatticeFourier
