import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Analytic
structure IsComplexCoordNorm {m : ℕ} (N : (Fin m → ℂ) → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ N t
  triangle : ∀ t t', N (t + t') ≤ N t + N t'
  smul_real : ∀ (c : ℝ) t, N ((c : ℂ) • t) = |c| * N t
  eq_zero : ∀ t, N t = 0 → t = 0
def HolomorphicFixedPointProperty : Prop :=
  ∀ (m k : ℕ) (N : (Fin m → ℂ) → ℝ) (Φ : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ))
    (U : Set (Fin k → ℂ)) (R : ℝ), 0 < R → IsOpen U → IsComplexCoordNorm N →
    (∀ z ∈ U, ∀ t, N t ≤ R → AnalyticAt ℂ Φ (t, z)) →
    (∀ z ∈ U, N (Φ (0, z)) ≤ R / 4) →
    (∀ z ∈ U, ∀ t t', N t ≤ R → N t' ≤ R → N (Φ (t, z) - Φ (t', z)) ≤ (1 / 2) * N (t - t')) →
    ∃ p : (Fin k → ℂ) → (Fin m → ℂ), ∀ z ∈ U,
      AnalyticAt ℂ p z ∧ Φ (p z, z) = p z ∧ N (p z) ≤ 2 * N (Φ (0, z)) ∧
        ∀ C : Set (Fin m → ℂ), IsClosed C → 0 ∈ C → (∀ t ∈ C, N t ≤ R → Φ (t, z) ∈ C) → p z ∈ C
end YangMills.Construction.Analytic
end
