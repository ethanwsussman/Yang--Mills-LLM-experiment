import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExponentialSums
def IteratedDerivBoundOfExponentialSum : Prop :=
  ∀ (c : (Fin 4 → ℤ) → ℂ) (ω φ : (Fin 4 → ℤ) → ℝ), (∀ d : ℕ, Summable fun z => ‖c z‖ * |ω z| ^ d) →
    ∀ (d : ℕ) (t : ℝ),
      ‖iteratedDeriv d (fun s : ℝ => ∑' z, c z * Complex.exp (Complex.I * ((s * ω z + φ z : ℝ) : ℂ))) t‖ ≤
        ∑' z, ‖c z‖ * |ω z| ^ d
end YangMills.Construction.ExponentialSums
end
