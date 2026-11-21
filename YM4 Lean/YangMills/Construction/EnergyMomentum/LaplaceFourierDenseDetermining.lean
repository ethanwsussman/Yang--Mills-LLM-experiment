import YangMills.Construction.EnergyMomentum.ContractionSemigroupUnitaryGroup
import YangMills.Construction.SpectralTheory.EuclideanBorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal
namespace YangMills.Construction.EnergyMomentum
open EuclideanSpectral
def LaplaceFourierDenseDetermining : Prop :=
  ∀ (μ : Measure EnergyMomentumSpace) [IsFiniteMeasure μ],
    (∀ f : EnergyMomentumSpace → ℂ, MemSqIntegrable μ f →
      ∃ g : ℕ → EnergyMomentumSpace → ℂ,
        (∀ n, g n ∈ laplaceFourierSpan) ∧ TendstoSqMean μ g f) ∧
    (∀ (ν : Measure EnergyMomentumSpace) [IsFiniteMeasure ν],
      (∀ (t : ℝ≥0) (k : Momentum3),
        ∫ x, laplaceFourierExp t k x ∂ν = ∫ x, laplaceFourierExp t k x ∂μ) → ν = μ)
end YangMills.Construction.EnergyMomentum
