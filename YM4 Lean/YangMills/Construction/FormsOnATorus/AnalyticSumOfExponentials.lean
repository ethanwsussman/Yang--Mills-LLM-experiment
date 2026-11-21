import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExponentialSums
def AnalyticAtSumOfExponentials : Prop :=
  ∀ (a : (Fin 4 → ℤ) → ℂ) (Λ : (Fin 4 → ℤ) → ℝ) (ℓ : (Fin 4 → ℤ) → ((Fin 4 → ℝ) →L[ℝ] ℂ)) (r : ℝ), 0 < r →
    (∀ z, ‖ℓ z‖ ≤ Λ z) → Summable (fun z => ‖a z‖ * Real.exp (Λ z * r)) →
    AnalyticAt ℝ (fun y => ∑' z, a z * Complex.exp (ℓ z y)) 0
end YangMills.Construction.ExponentialSums
end
