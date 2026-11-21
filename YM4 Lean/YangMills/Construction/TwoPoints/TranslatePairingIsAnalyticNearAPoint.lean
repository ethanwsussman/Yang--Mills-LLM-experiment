import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def ShiftPairingLocallyAnalytic.Statement : Prop :=
  ∀ (scale : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm scale S → ∀ ξ : AmbientSpace, ξ ≠ 0 → ∃ O : Set AmbientSpace, IsOpen O ∧
      euclidClosedBall ξ (2 * (euclidNorm ξ / 32)) ⊆ O ∧
      O ⊆ {z | 2 * (euclidNorm ξ / 32) < euclidNorm z} ∧
      ∀ φ₁ ∈ cc1NearZero (euclidNorm ξ / 32), ∀ φ₂ ∈ cc1NearZero (euclidNorm ξ / 32),
        AnalyticOnNhd ℝ (shiftPairing S φ₁ φ₂) O
end YangMills.Construction.TwoPoints
end
