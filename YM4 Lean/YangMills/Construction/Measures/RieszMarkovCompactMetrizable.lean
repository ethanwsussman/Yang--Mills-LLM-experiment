import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
namespace YangMills.Construction.Measures.RieszMarkov
def positiveFunctional_representation : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X],
    (∀ L : C(X, ℝ) →ₗ[ℝ] ℝ, (∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) →
      (∃! μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), L f = ∫ x, f x ∂μ) ∧
      (L 1 = 1 → ∀ μ : Measure X, IsFiniteMeasure μ →
        (∀ f : C(X, ℝ), L f = ∫ x, f x ∂μ) → IsProbabilityMeasure μ)) ∧
    (∀ L : C(X, ℂ) →ₗ[ℂ] ℂ, (∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ L f) →
      (∃! μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), L f = ∫ x, f x ∂μ) ∧
      (L 1 = 1 → ∀ μ : Measure X, IsFiniteMeasure μ →
        (∀ f : C(X, ℂ), L f = ∫ x, f x ∂μ) → IsProbabilityMeasure μ)) ∧
    (∀ μ ν : Measure X, IsFiniteMeasure μ → IsFiniteMeasure ν →
      (∀ f : C(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν) ∧
    (∀ μ ν : Measure X, IsFiniteMeasure μ → IsFiniteMeasure ν →
      (∀ f : C(X, ℂ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν)
end YangMills.Construction.Measures.RieszMarkov
