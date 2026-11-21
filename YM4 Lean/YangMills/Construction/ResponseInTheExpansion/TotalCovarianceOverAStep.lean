import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
def LawOfTotalCovarianceWithIncrement : Prop :=
  ∀ (Ω Ω' : Type) (𝒢 : MeasurableSpace Ω') [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (π : Ω' → Ω)
    (f₁ f₂ : Ω → ℝ) (g₁ g₂ : Ω' → ℝ) (C : ℝ),
    MeasurePreserving π ν μ → 𝒢 ≤ mΩ' →
    AEStronglyMeasurable f₁ μ → AEStronglyMeasurable f₂ μ →
    (∀ᵐ ω ∂μ, |f₁ ω| ≤ C) → (∀ᵐ ω ∂μ, |f₂ ω| ≤ C) →
    AEStronglyMeasurable g₁ ν → AEStronglyMeasurable g₂ ν →
    (∀ᵐ u ∂ν, |g₁ u| ≤ C) → (∀ᵐ u ∂ν, |g₂ u| ≤ C) →
    ∫ u, g₁ u ∂ν = 0 → ∫ u, g₂ u ∂ν = 0 →
    ∫ u, f₂ (π u) * g₁ u ∂ν = 0 → ∫ u, f₁ (π u) * g₂ u ∂ν = 0 →
    cov[f₁, f₂; μ] =
      cov[ν[fun u => f₁ (π u) + g₁ u | 𝒢], ν[fun u => f₂ (π u) + g₂ u | 𝒢]; ν] +
        (∫ u, ((ν[fun u => (f₁ (π u) + g₁ u) * (f₂ (π u) + g₂ u) | 𝒢]) u -
            (ν[fun u => f₁ (π u) + g₁ u | 𝒢]) u * (ν[fun u => f₂ (π u) + g₂ u | 𝒢]) u) ∂ν -
          ∫ u, g₁ u * g₂ u ∂ν)
end YangMills.Construction.WeightedResponses
end
