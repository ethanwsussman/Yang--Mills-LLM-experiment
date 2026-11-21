import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Schwinger
structure ClusterBound where
  value : ℕ → ℝ → ℝ → ℝ
  value_nonneg : ∀ n : ℕ, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ value n d R
  value_anti : ∀ n : ℕ, 2 ≤ n → ∀ d d' R : ℝ, 0 < d → d ≤ d' → 0 < R →
    value n d' R ≤ value n d R
end YangMills.Construction.Schwinger
