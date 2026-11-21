import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.ParametricMinima
def StrictMinimumPersistsAnalytically : Prop :=
  ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (f : E × P → ℝ) (p₀ : P),
    AnalyticAt ℝ f (0, p₀) →
    fderiv ℝ (fun e => f (e, p₀)) 0 = 0 →
    (∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ fun e => f (e, p₀)) 0 v v) →
    ∃ (x : P → E) (r : ℝ), 0 < r ∧ AnalyticAt ℝ x p₀ ∧ x p₀ = 0 ∧
      ∀ᶠ p in 𝓝 p₀, ‖x p‖ < r ∧
        (∀ e : E, ‖e‖ < r → e ≠ x p → f (x p, p) < f (e, p)) ∧
        ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ fun e => f (e, p)) (x p) v v
end YangMills.Construction.ParametricMinima
end
