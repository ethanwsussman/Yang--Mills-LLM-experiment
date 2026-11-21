import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatioUnderIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.IteratedIntegral
theorem integral_mul_integral_le_of_mul_le {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    {f₁ g₀ : X → ℝ} {f₀ g₁ : Y → ℝ} {c : ℝ} (hf₁ : Integrable f₁ μ) (hg₀ : Integrable g₀ μ)
    (hf₀ : Integrable f₀ ν) (hg₁ : Integrable g₁ ν)
    (h : ∀ x y, f₁ x * f₀ y ≤ c * (g₀ x * g₁ y)) :
    (∫ x, f₁ x ∂μ) * (∫ y, f₀ y ∂ν) ≤ c * ((∫ x, g₀ x ∂μ) * ∫ y, g₁ y ∂ν) := by
  have inner : ∀ x, f₁ x * (∫ y, f₀ y ∂ν) ≤ c * g₀ x * ∫ y, g₁ y ∂ν := by
    intro x
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_mono (hf₀.const_mul _) (hg₁.const_mul _) fun y => ?_
    have := h x y
    simp only
    linarith [this, show c * (g₀ x * g₁ y) = c * g₀ x * g₁ y by ring]
  have houter := integral_mono (μ := μ) (hf₁.mul_const (∫ y, f₀ y ∂ν))
    ((hg₀.const_mul c).mul_const (∫ y, g₁ y ∂ν)) inner
  rw [integral_mul_const, integral_mul_const, integral_const_mul] at houter
  linarith [houter, show c * (∫ x, g₀ x ∂μ) * (∫ y, g₁ y ∂ν) =
    c * ((∫ x, g₀ x ∂μ) * ∫ y, g₁ y ∂ν) by ring]
theorem crossRatioIntegralStatement_holds : CrossRatioIntegralStatement := by
  intro A₁ A₀ B₁ B₀ _ _ _ _ μ₁ μ₀ ν₁ ν₀ R₁₁ R₁₀ R₀₁ R₀₀ c h11 h10 h01 h00 i11 i10 i01 i00 hR
  refine integral_mul_integral_le_of_mul_le i11 i10 i00 i01 fun a₁ a₀ => ?_
  have key := integral_mul_integral_le_of_mul_le (h11 a₁) (h01 a₀) (h00 a₀) (h10 a₁) fun b₁ b₀ => by
    have := hR a₁ a₀ b₁ b₀
    linarith [this, show c * (R₀₁ a₀ b₁ * R₁₀ a₁ b₀) = c * (R₁₀ a₁ b₀ * R₀₁ a₀ b₁) by ring]
  rw [mul_comm (∫ b, R₁₀ a₁ b ∂ν₀)]
  exact key
end YangMills.Construction.IteratedIntegral
end
