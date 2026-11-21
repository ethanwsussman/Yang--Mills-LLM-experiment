import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace YangMills.Construction.Measures.CompactMetric
def measuresAndContinuousFunctions : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X],
    (∀ μ μ' : Measure X, IsFiniteMeasure μ → IsFiniteMeasure μ' →
      (∀ g : C(X, ℝ), ∫ x, g x ∂μ = ∫ x, g x ∂μ') → μ = μ') ∧
    (∀ P : ℕ → Measure X, (∀ n, IsProbabilityMeasure (P n)) →
      ∃ (φ : ℕ → ℕ) (Q : Measure X), StrictMono φ ∧ IsProbabilityMeasure Q ∧
        ∀ G : C(X, ℂ),
          Tendsto (fun k => ∫ x, G x ∂(P (φ k))) atTop (𝓝 (∫ x, G x ∂Q))) ∧
    (∃ e : ℕ → C(X, ℝ), (∀ n x, e n x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (G : C(X, ℂ)) (δ : ℝ), 0 < δ →
        ∃ (S : Finset ℕ) (a : ℕ → ℂ), ∀ x, ‖G x - ∑ n ∈ S, a n * (e n x : ℂ)‖ ≤ δ)
end YangMills.Construction.Measures.CompactMetric
