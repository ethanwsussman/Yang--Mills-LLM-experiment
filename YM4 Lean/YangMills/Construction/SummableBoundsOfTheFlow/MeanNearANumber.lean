import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfACutMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
def ExpectationNearConstant : Prop :=
  ∀ (ι : Type) [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (Φ f : BondField ι → ℝ) (D : ι → ℝ) (f₀ t m₂ : ℝ),
    0 < ρ → 0 < t → IsPositiveUnitalForm ρ p Φ → IsBoundedContinuousOn ι ρ f → (∀ b, 0 ≤ D b) →
    (∀ η ∈ openPolyball ι ρ, |f η - f₀| ≤ ∑ b, ‖η b‖ * D b) →
    (∀ b, ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ m₂) →
    |ballExpectation (cutoffFactor ρ p) Φ f - f₀| ≤ (∑ b, D b) * (t / 2 + m₂ / (2 * t))
end Estimates
end YangMills.Construction
end
