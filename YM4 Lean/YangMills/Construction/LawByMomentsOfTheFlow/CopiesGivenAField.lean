import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace MomentMethod
def conditionalCopyCovarianceStatement : Prop :=
  ∀ (Ω : Type) [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : MeasurableSpace Ω) (σ σ' : Ω → Ω),
    𝒢 ≤ m₀ → @MeasurePreserving _ _ m₀ m₀ σ μ μ → @MeasurePreserving _ _ m₀ m₀ σ' μ μ → (∀ ω, σ' (σ ω) = ω) → (∀ ω, σ (σ' ω) = ω) →
    @Measurable _ _ 𝒢 𝒢 σ → @Measurable _ _ 𝒢 𝒢 σ' →
    ∀ (W W' Y Yb : Ω → ℝ) (C δ A ε : ℝ), StronglyMeasurable[𝒢] W → StronglyMeasurable[𝒢] W' → (∀ ω, |W ω| ≤ C) → (∀ ω, |W' ω| ≤ C) →
      MemLp Y 2 μ → MemLp Yb 2 μ → @Measurable _ _ m₀ _ Yb → (∃ B : ℝ, ∀ ω, |Yb ω| ≤ B) → 0 ≤ A → 0 ≤ ε →
      ∫ ω, Y ω ^ 2 ∂μ ≤ A ^ 2 → ∫ ω, Yb ω ^ 2 ∂μ ≤ A ^ 2 → ∫ ω, (Y ω - Yb ω) ^ 2 ∂μ ≤ ε ^ 2 →
      (∀ᵐ ω ∂μ, |(μ[fun z => Yb z * Yb (σ z) | 𝒢]) ω - (μ[Yb | 𝒢]) ω * (μ[Yb ∘ σ | 𝒢]) ω| ≤ δ) →
      |∫ ω, W ω * W' ω * ((Y ω - (μ[Y | 𝒢]) ω) * (Y (σ ω) - (μ[Y | 𝒢]) (σ ω))) ∂μ| ≤ C ^ 2 * (δ + 8 * A * ε)
end MomentMethod
end YangMills.Construction
end
