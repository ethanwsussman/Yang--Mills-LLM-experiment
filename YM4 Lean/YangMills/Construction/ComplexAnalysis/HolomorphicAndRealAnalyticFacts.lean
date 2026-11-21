import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open YangMills.Construction.Coordinates
def HolomorphicAndRealAnalyticFacts : Prop :=
  (∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (U : Set ℂ)
      (g : ℂ → X → ℂ),
    IsOpen U → (∃ M : ℝ, ∀ w ∈ U, ∀ x, ‖g w x‖ ≤ M) →
    Measurable (fun p : U × X => g p.1 p.2) →
    (∀ x, DifferentiableOn ℂ (fun w => g w x) U) →
    DifferentiableOn ℂ (fun w => ∫ x, g w x ∂ν) U) ∧
  (∀ ψ : ℝ → ℂ,
    (∀ s : ℝ, ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (s : ℂ) ρ) ∧
      ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (s : ℂ) ρ → h r = ψ r) →
    (∃ a b : ℝ, a < b ∧ ∀ r ∈ Ioo a b, ψ r = 0) →
    ∀ r, ψ r = 0) ∧
  (∀ (k : ℕ), 1 ≤ k → ∀ (U : Set (ComplexCoordinates k)) (f : ComplexCoordinates k → ℂ),
    ComplexCoordinates.IsRealAnalyticIn (N' := 1) U (fun z _ => f z) →
    ∀ a ∈ U, ∃ (W : Set (ComplexCoordinates k)) (h : ComplexCoordinates k → ℂ),
      IsOpen W ∧ a ∈ W ∧ W ∩ ComplexCoordinates.realLocus k ⊆ U ∧
      ComplexCoordinates.IsHolomorphicIn (N' := 1) W (fun z _ => h z) ∧
      ∀ z ∈ W ∩ ComplexCoordinates.realLocus k, h z = f z)
end YangMills.Construction.ComplexAnalysis
