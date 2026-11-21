import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Analytic
def vanishingOnRealPointsStatement : Prop :=
  ∀ (k : ℕ) (r : ℝ) (g : (Fin k → ℂ) → ℂ),
    (∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → AnalyticAt ℂ g ζ) →
    (∀ x : Fin k → ℝ, ∑ l, |x l| < r → g (fun l => (x l : ℂ)) = 0) →
    ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → g ζ = 0
end YangMills.Construction.Analytic
end
