import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def SecondDerivGradientInvariant : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (T : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → ℝ) (s : ℝ)
    (X₀ X₁ : imaginaryQuaternions) (φ₀ φ₁ : F.Site j → ℝ) (a₀ a₁ : F.Site j → Fin 4 → ℝ),
    (∀ b, b ∈ T) → (∀ i, F.period j i ≠ 0) → 0 < s → ContDiffThreeAlongBonds G (uniformField F j) →
    (∀ (W : F.GaugeField j) (γ : F.Site j → UnitQuaternion), IsSmallCurvature s W → G (gaugeTransform γ W) = G W) →
    ‖X₀‖ = 1 → ‖X₁‖ = 1 →
    ∑ b ∈ T, ∑ b' ∈ T, bondDeriv G (uniformField F j) ![b, b'] ![X₀, X₁] *
        (a₀ b.1 b.2 + (φ₀ b.1 - φ₀ (b.1 + unitStep j b.2))) *
        (a₁ b'.1 b'.2 + (φ₁ b'.1 - φ₁ (b'.1 + unitStep j b'.2))) =
      ∑ b ∈ T, ∑ b' ∈ T, bondDeriv G (uniformField F j) ![b, b'] ![X₀, X₁] * a₀ b.1 b.2 * a₁ b'.1 b'.2
end YangMills.Construction.ColdStepAtMirrorFrames
end
