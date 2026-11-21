import YangMills.Construction.ResponseInTheExpansion.HeatSumOnALine
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
def heatLatticeTerm (N : ℕ) (t : ℝ) (z : Fin 4 → ℝ) (a b : Fin 4) (k : Fin 4 → ℤ) : ℂ :=
  ((circleMomentum N (k a) * circleMomentum N (k b) *
      Real.exp (-(t * ∑ i, circleMomentum N (k i) ^ 2)) : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ))
def heatKernelHessian (t : ℝ) (z : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ((if a = b then 1 / (2 * t) else 0) - z a * z b / (4 * t ^ 2)) *
    Real.exp (-((∑ i, z i ^ 2) / (4 * t))) / (16 * Real.pi ^ 2 * t ^ 2)
def poissonSummationHeatLatticeStatement : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (t : ℝ) (z : Fin 4 → ℝ) (a b : Fin 4), 8 ≤ N → 1 ≤ t → t ≤ (N : ℝ) ^ 2 →
    ∑ i, z i ^ 2 ≤ ((N : ℝ) / 8) ^ 2 →
    Summable (heatLatticeTerm N t z a b) ∧
    ‖((N : ℂ) ^ 4)⁻¹ * ∑' k, heatLatticeTerm N t z a b k - (heatKernelHessian t z a b : ℂ)‖ ≤
      C * (t ^ 3)⁻¹ * Real.exp (-((N : ℝ) ^ 2 / (11 * t)))
end YangMills.Construction.LatticeFourier
