import YangMills.Construction.EnergyMomentum.ContractionSemigroupUnitaryGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.EnergyMomentum
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure IsSpectralMeasure (S : ℝ≥0 → H →L[ℂ] H) (U : Momentum3 → H →L[ℂ] H) (ψ : H)
    (μ : Measure EnergyMomentumSpace) : Prop where
  isFiniteMeasure : IsFiniteMeasure μ
  inner_eq_integral : ∀ t x, ⟪ψ, (S t * U x) ψ⟫_ℂ = ∫ p, laplaceFourierExp t x p ∂μ
def spectralMeasure (S : ℝ≥0 → H →L[ℂ] H) (U : Momentum3 → H →L[ℂ] H) (ψ : H) :
    Measure EnergyMomentumSpace :=
  Classical.epsilon (IsSpectralMeasure S U ψ)
end Operators
namespace SpectralMeasure
def Statement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : ℝ≥0 → H →L[ℂ] H) (U : Momentum3 → H →L[ℂ] H),
    IsContractionSemigroupWithUnitaryGroup S U → ∀ ψ : H,
      IsSpectralMeasure S U ψ (spectralMeasure S U ψ) ∧
      (∀ μ : Measure EnergyMomentumSpace, IsSpectralMeasure S U ψ μ → μ = spectralMeasure S U ψ) ∧
      (spectralMeasure S U ψ).real Set.univ = ‖ψ‖ ^ 2
end SpectralMeasure
end YangMills.Construction.EnergyMomentum
