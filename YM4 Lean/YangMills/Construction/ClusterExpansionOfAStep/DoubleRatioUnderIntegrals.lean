import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.IteratedIntegral
def CrossRatioIntegralStatement : Prop :=
  ∀ (X₁ X₀ Y₁ Y₀ : Type) [MeasurableSpace X₁] [MeasurableSpace X₀] [MeasurableSpace Y₁] [MeasurableSpace Y₀]
    (μ₁ : Measure X₁) (μ₀ : Measure X₀) (ν₁ : Measure Y₁) (ν₀ : Measure Y₀)
    (f₁₁ : X₁ → Y₁ → ℝ) (f₁₀ : X₁ → Y₀ → ℝ) (f₀₁ : X₀ → Y₁ → ℝ) (f₀₀ : X₀ → Y₀ → ℝ) (c : ℝ),
    (∀ x, Integrable (f₁₁ x) ν₁) → (∀ x, Integrable (f₁₀ x) ν₀) → (∀ x, Integrable (f₀₁ x) ν₁) →
    (∀ x, Integrable (f₀₀ x) ν₀) →
    Integrable (fun x => ∫ y, f₁₁ x y ∂ν₁) μ₁ → Integrable (fun x => ∫ y, f₁₀ x y ∂ν₀) μ₁ →
    Integrable (fun x => ∫ y, f₀₁ x y ∂ν₁) μ₀ → Integrable (fun x => ∫ y, f₀₀ x y ∂ν₀) μ₀ →
    (∀ x₁ x₀ y₁ y₀, f₁₁ x₁ y₁ * f₀₀ x₀ y₀ ≤ c * (f₁₀ x₁ y₀ * f₀₁ x₀ y₁)) →
    (∫ x, ∫ y, f₁₁ x y ∂ν₁ ∂μ₁) * (∫ x, ∫ y, f₀₀ x y ∂ν₀ ∂μ₀) ≤
      c * ((∫ x, ∫ y, f₁₀ x y ∂ν₀ ∂μ₁) * ∫ x, ∫ y, f₀₁ x y ∂ν₁ ∂μ₀)
end YangMills.Construction.IteratedIntegral
end
