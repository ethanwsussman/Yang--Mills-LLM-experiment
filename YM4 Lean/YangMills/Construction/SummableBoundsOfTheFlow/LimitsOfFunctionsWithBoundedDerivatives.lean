import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.UniformLimits
def IteratedFDerivTendstoOfUniformLimit : Prop :=
  ∀ (k : ℕ) (r C : ℝ) (ι : Type) (L : Filter ι) [L.NeBot] (f : ι → (Fin k → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ), 0 < r →
    (∀ᶠ i in L, ContDiffOn ℝ 3 (f i) (Metric.ball 0 r) ∧
      ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C) →
    TendstoUniformlyOn f g L (Metric.ball 0 r) →
    ∀ (j : ℕ) (v : Fin j → Fin k → ℝ), j ≤ 2 →
      Filter.Tendsto (fun i => iteratedFDeriv ℝ j (f i) 0 v) L (𝓝 (iteratedFDeriv ℝ j g 0 v))
end YangMills.Construction.UniformLimits
end
