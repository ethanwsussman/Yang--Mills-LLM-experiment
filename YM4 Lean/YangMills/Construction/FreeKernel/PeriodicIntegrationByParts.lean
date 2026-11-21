import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex
def PeriodicFourierIntegrationByParts : Prop :=
  ∀ (n : ℕ) (f : ℝ → ℂ) (m : ℤ), m ≠ 0 → ContDiff ℝ n f → Function.Periodic f (2 * Real.pi) →
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)) * f θ =
      (I / (m : ℂ)) ^ n *
        ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)) * iteratedDeriv n f θ
end YangMills.Construction.FreeKernel
end
