import YangMills.Construction.TwoPoints.ThirdPropertyAndFamiliesOfSpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.SpectralCalculus (SpectralPlane)
def HolomorphicParametricIntegral.Statement : Prop :=
  ∀ (X : Set SpectralPlane), MeasurableSet X → ∀ (ρ : Measure X) (U : Set ℂ), IsOpen U →
    ∀ F : ℂ → X → ℂ,
      (∀ z ∈ U, Measurable (F z)) →
      (∀ x : X, IsHolomorphicOnOne U (fun z => F z x)) →
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ g : X → ℝ, (∀ x, 0 ≤ g x) ∧ Integrable g ρ ∧
        ∀ z ∈ K, ∀ x, ‖F z x‖ ≤ g x) →
      (∀ z ∈ U, Integrable (F z) ρ) ∧
        IsHolomorphicOnOne U (fun z => ∫ x, F z x ∂ρ)
end YangMills.Construction.TwoPoints
end
