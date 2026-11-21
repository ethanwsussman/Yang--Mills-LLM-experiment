import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates
def HolomorphicParametricIntegral : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    ∀ U : Set (ComplexCoordinates n), IsOpen U → ∀ F : X × ComplexCoordinates n → ℂ,
      (∀ z ∈ U, Measurable fun x => F (x, z)) →
      (∀ x, IsHolomorphicIn (N' := 1) U fun z _ => F (x, z)) →
      (∀ a ∈ U, ∃ V ∈ 𝓝 a, V ⊆ U ∧ ∃ C : ℝ, ∀ x, ∀ z ∈ V, ‖F (x, z)‖ ≤ C) →
      (∀ z ∈ U, Integrable (fun x => F (x, z)) μ) ∧
        IsHolomorphicIn (N' := 1) U fun z _ => ∫ x, F (x, z) ∂μ
end YangMills.Construction.Coordinates.ComplexCoordinates
end
