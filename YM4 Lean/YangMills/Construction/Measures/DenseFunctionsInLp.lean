import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
namespace YangMills.Construction.Measures.DenseInLp
def ApproximatesLp {X : Type} [MeasurableSpace X] (μ : Measure X) (A : Set (X → ℂ)) :
    Prop :=
  ∀ p : ℝ≥0∞, (p = 1 ∨ p = 2) → ∀ (g : Lp ℂ p μ) (ε : ℝ), 0 < ε →
    ∃ f ∈ A, ∃ hf : MemLp f p μ, ‖g - hf.toLp f‖ ≤ ε
def boundedConvergence_dense : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsFiniteMeasure μ →
    (∀ (A : Submodule ℂ (X → ℂ)) (S : Set (Set X)),
      (∀ f ∈ A, Measurable f ∧ ∃ c : ℝ, ∀ x, ‖f x‖ ≤ c) →
      (∀ E ∈ S, MeasurableSet E) →
      (∀ E ∈ S, ∀ E' ∈ S, E ∩ E' ∈ S) →
      Set.univ ∈ S →
      MeasurableSpace.generateFrom S = borel X →
      (∀ E ∈ S, ∃ f : ℕ → X → ℂ, (∀ n, 1 ≤ n → f n ∈ A ∧ ∀ x, ‖f n x‖ ≤ 1) ∧
        ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (E.indicator 1 x))) →
      ApproximatesLp μ (A : Set (X → ℂ))) ∧
    ApproximatesLp μ {f : X → ℂ | Continuous f}
end YangMills.Construction.Measures.DenseInLp
