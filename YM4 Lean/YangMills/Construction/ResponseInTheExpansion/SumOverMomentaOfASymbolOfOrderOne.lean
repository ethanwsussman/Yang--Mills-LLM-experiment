import YangMills.Construction.ResponseInTheExpansion.SymbolOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open LinearResponse TorusFields
open Classical
structure IsSymbolOfOrder (B : ℕ → ℝ) (a : ℝ) (b : (Fin 4 → ℝ) → ℂ) : Prop where
  smooth : ∀ r : ℕ, ContDiffOn ℝ r b {p | ∀ w : Fin 4 → ℤ, p ≠ fun i => 2 * Real.pi * (w i : ℝ)}
  deriv_le : ∀ (r : ℕ) (p : Fin 4 → ℝ), p ≠ 0 → (∀ i, |p i| ≤ Real.pi) →
    ‖iteratedFDeriv ℝ r b p‖ ≤ B r * sqNorm p ^ ((a - r) / 2)
def nonzeroMomentumWave (N : ℕ) [NeZero N] (b : (Fin 4 → ℝ) → ℂ) (z : Fin 4 → ℝ) : ℂ :=
  ((N : ℂ) ^ 4)⁻¹ * ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
    b (dualMomentum j) * Complex.exp (Complex.I * (∑ i, dualMomentum j i * z i : ℝ))
def orderOneMomentumSumStatement : Prop :=
  ∀ B : ℕ → ℝ, ∃ C N₀ : ℝ, ∀ (N : ℕ) [NeZero N] (b : (Fin 4 → ℝ) → ℂ) (z : Fin 4 → ℝ), N₀ ≤ N →
    IsSymbolOfOrder B 1 b →
    (∀ (p : Fin 4 → ℝ) (i : Fin 4), (∀ w : Fin 4 → ℤ, p ≠ fun l => 2 * Real.pi * (w l : ℝ)) →
      b (p + Pi.single i (2 * Real.pi)) * Complex.exp (Complex.I * (2 * Real.pi * z i : ℝ)) = b p) →
    1 ≤ sqNorm z → sqNorm z ≤ ((N : ℝ) / 8) ^ 2 →
    ‖nonzeroMomentumWave N b z‖ ≤ C * (sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)))
end YangMills.Construction.ResponseInTheExpansion
end
