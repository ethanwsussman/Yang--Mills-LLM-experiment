import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Measures.CompactMetricProbability
open YangMills.Construction.LatticePhases
def testDistance {X : Type} [TopologicalSpace X] [MeasurableSpace X] (F : ℕ+ → C(X, ℂ))
    (ρ ρ' : ProbMeasure X) : ℝ :=
  ∑' k : ℕ+, (2 : ℝ)⁻¹ ^ (k : ℕ) * min 1 ‖ρ.eval (F k) - ρ'.eval (F k)‖
def CompactMetricProbabilityFacts : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X],
    ((∃ D : Set X, D.Countable ∧ Dense D) ∧
      (∃ B : Set (Set X), B.Countable ∧
        (∀ b ∈ B, ∃ (x : X) (r : ℝ), 0 < r ∧ b = Metric.ball x r) ∧
        ∀ O : Set X, IsOpen O → O = ⋃₀ {b ∈ B | b ⊆ O}) ∧
      TopologicalSpace.SeparableSpace C(X, ℂ)) ∧
    (∀ ρ : ProbMeasure X,
      Dense (Set.range (ContinuousMap.toLp 1 ρ.toMeasure ℂ : C(X, ℂ) →L[ℂ] ρ.Lp1)) ∧
      Dense (Set.range (ContinuousMap.toLp 2 ρ.toMeasure ℂ : C(X, ℂ) →L[ℂ] ρ.Lp2))) ∧
    (∀ H : Submodule ℂ (X → ℂ),
      (∀ f ∈ H, Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      (∀ F : C(X, ℂ), (F : X → ℂ) ∈ H) →
      (∀ (u : ℕ → X → ℂ) (g : X → ℂ), (∀ n, u n ∈ H) → (∃ C : ℝ, ∀ n x, ‖u n x‖ ≤ C) →
        (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) → g ∈ H) →
      (H : Set (X → ℂ)) = {f | Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C}) ∧
    (∀ S : Set C(X, ℂ), Dense S → ∀ ρ ρ' : ProbMeasure X,
      (∀ F ∈ S, ρ.eval F = ρ'.eval F) → ρ = ρ') ∧
    (∀ F : ℕ+ → C(X, ℂ), Dense (Set.range F) →
      (∃ d : MetricSpace (ProbMeasure X),
        (∀ ρ ρ' : ProbMeasure X, @dist _ d.toDist ρ ρ' = testDistance F ρ ρ') ∧
        d.toUniformSpace.toTopologicalSpace =
          (ProbMeasure.instWeakTopology : TopologicalSpace (ProbMeasure X))) ∧
      @CompactSpace (ProbMeasure X) ProbMeasure.instWeakTopology ∧
      @borel (ProbMeasure X) ProbMeasure.instWeakTopology =
        ⨆ k : ℕ+, MeasurableSpace.comap (fun ρ : ProbMeasure X => ρ.eval (F k)) (borel ℂ))
end YangMills.Construction.Measures.CompactMetricProbability
