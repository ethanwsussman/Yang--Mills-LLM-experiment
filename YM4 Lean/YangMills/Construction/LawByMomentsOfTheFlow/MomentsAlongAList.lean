import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace MomentMethod
def sumAlong {X ι : Type} (e : ι → X → ℝ) (l : List ι) (x : X) : ℝ := (l.map fun c => e c x).sum
def momentBoundStatement : Prop :=
  (∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (ι : Type) (e : ι → X → ℝ),
    (∀ c, Measurable (e c)) → (∀ c x, 0 ≤ e c x) → ∀ (l₁ l₂ : List ι) (q : ℕ) (b b' ε a₀ a₁ a₂ a₃ c₀ K : ℝ), 1 ≤ q →
    0 ≤ b → 0 ≤ b' → 0 < ε → 0 ≤ a₀ → 0 ≤ a₁ → 0 ≤ a₂ → 0 ≤ a₃ → 0 ≤ c₀ → 0 ≤ K →
    (∀ c, eLpNorm (e c) ((2 * q : ℕ) : ENNReal) μ ≤ ENNReal.ofReal b) →
    (∀ c, eLpNorm (e c) ((20 * q : ℕ) : ENNReal) μ ≤ ENNReal.ofReal b') →
    ∀ g : X → ℝ, (∀ᵐ x ∂μ, |g x| ≤ K * (a₀ + a₁ * sumAlong e l₁ x + sumAlong e l₂ x) ^ 2 + c₀ +
      a₂ * (a₀ + a₁ * sumAlong e l₁ x + sumAlong e l₂ x) + a₃ * sumAlong e l₁ x +
      20 * sumAlong (fun c x => (e c x / ε) ^ 20) l₂ x) →
    eLpNorm g (q : ENNReal) μ ≤ ENNReal.ofReal (K * (a₀ + a₁ * (l₁.length * b) + l₂.length * b) ^ 2 + c₀ +
      a₂ * (a₀ + a₁ * (l₁.length * b) + l₂.length * b) + a₃ * (l₁.length * b) + 20 * (l₂.length * (b' / ε) ^ 20))) ∧
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (k : ℕ) (C x : ℝ), 1 ≤ k → 0 < x → (∀ y, 0 ≤ f y) →
    ∫⁻ y, ENNReal.ofReal (f y ^ (2 * k)) ∂μ ≤ ENNReal.ofReal (C * (x ^ k)⁻¹) →
    eLpNorm f ((2 * k : ℕ) : ENNReal) μ ≤ ENNReal.ofReal ((|C| + 1) * x ^ (-(1 / 2) : ℝ))
end MomentMethod
end YangMills.Construction
end
