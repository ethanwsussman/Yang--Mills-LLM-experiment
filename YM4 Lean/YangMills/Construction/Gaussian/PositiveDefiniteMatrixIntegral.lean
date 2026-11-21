import Mathlib
set_option autoImplicit false
open scoped Matrix
namespace YangMills.Construction.Gaussian.PosDefMatrix
def RealGaussianIntegral : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
    ∫ x : Fin n → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) =
      (2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt A.det
end YangMills.Construction.Gaussian.PosDefMatrix
