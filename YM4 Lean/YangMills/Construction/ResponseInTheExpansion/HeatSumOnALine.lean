import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
def circleMomentum (N : ℕ) (n : ℤ) : ℝ := 2 * Real.pi * n / N
def thetaTerm (N : ℕ) (t x : ℝ) (k : ℕ) (n : ℤ) : ℂ :=
  ((circleMomentum N n ^ k * Real.exp (-(t * circleMomentum N n ^ 2)) : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((circleMomentum N n * x : ℝ) : ℂ))
def gaussianProfile (t : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  match k with
  | 0 => Real.exp (-(y ^ 2 / (4 * t)))
  | 1 => -(y / (2 * t)) * Real.exp (-(y ^ 2 / (4 * t)))
  | _ => (y ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * Real.exp (-(y ^ 2 / (4 * t)))
def heatKernelDeriv (t x : ℝ) (k : ℕ) : ℂ :=
  (-Complex.I) ^ k * (((Real.sqrt (4 * Real.pi * t))⁻¹ * gaussianProfile t k x : ℝ) : ℂ)
def poissonSummationHeatStatement : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (t x : ℝ), 8 ≤ N → 1 ≤ t → t ≤ (N : ℝ) ^ 2 → |x| ≤ (N : ℝ) / 8 → ∀ k ≤ 2,
    Summable (thetaTerm N t x k) ∧
    ‖(N : ℂ)⁻¹ * ∑' n, thetaTerm N t x k n - heatKernelDeriv t x k‖ ≤
      C * (Real.sqrt t)⁻¹ ^ (k + 1) * Real.exp (-((N : ℝ) ^ 2 / (11 * t))) ∧
    ‖heatKernelDeriv t x k‖ ≤ C * (Real.sqrt t)⁻¹ ^ (k + 1)
end YangMills.Construction.LatticeFourier
