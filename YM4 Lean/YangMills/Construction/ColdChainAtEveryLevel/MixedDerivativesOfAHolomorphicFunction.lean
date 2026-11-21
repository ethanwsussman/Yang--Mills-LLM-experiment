import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Analytic
def CauchyMixedDerivativeDifferenceProperty : Prop :=
  ∀ (k m : ℕ) (w : Fin m → Fin k) (i₀ : Fin m) (g : (Fin k → ℂ) → ℂ) (h : (Fin k → ℝ) → ℝ) (r M : ℝ), 0 < r →
    (∀ z : Fin k → ℂ, ∑ l, ‖z l‖ < r → AnalyticAt ℂ g z) →
    (∀ᶠ x in nhds (0 : Fin k → ℝ), g (fun l => (x l : ℂ)) = (h x : ℂ)) →
    (∀ z : Fin k → ℂ, ∑ l, ‖z l‖ < r → ‖g z - g (Function.update z (w i₀) 0)‖ ≤ M) →
    |iteratedFDeriv ℝ m h 0 (fun l => Pi.single (w l) 1)| ≤ M * (((m : ℝ) + 1) / r) ^ m
end YangMills.Construction.Analytic
end
