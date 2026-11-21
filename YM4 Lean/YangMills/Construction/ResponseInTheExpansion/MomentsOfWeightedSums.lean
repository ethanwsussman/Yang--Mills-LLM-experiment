import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace Moments
def EvenMomentOfWeightedSumBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Type) [Fintype κ]
    (c : κ → ℝ) (g : κ → Ω → ℝ) (f : Ω → ℝ) (r : ℕ) (D : ℝ),
    1 ≤ r → (∀ i, 0 ≤ c i) → 0 ≤ D → AEStronglyMeasurable f μ →
    (∀ i, Integrable (fun ω => g i ω ^ (2 * r)) μ) → (∀ i, ∫ ω, g i ω ^ (2 * r) ∂μ ≤ D) →
    (∀ᵐ ω ∂μ, |f ω| ≤ ∑ i, c i * |g i ω|) →
    Integrable (fun ω => f ω ^ (2 * r)) μ ∧ ∫ ω, f ω ^ (2 * r) ∂μ ≤ (∑ i, c i) ^ (2 * r) * D
end Moments
end YangMills.Construction
end
