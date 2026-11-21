import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ExpSumProductKernel
def kernelForm {X Γ : Type} [MeasurableSpace X] [Fintype Γ] (ν : Measure X) (t : Γ → X → ℝ)
    (g h : X → ℂ) : ℂ :=
  ∫ p : X × X, starRingEnd ℂ (g p.2) * h p.1 * (Real.exp (∑ γ, t γ p.1 * t γ p.2) : ℂ) ∂ν.prod ν
def PositivityStatement : Prop :=
  ∀ (X Γ : Type) [MeasurableSpace X] [Fintype Γ] (ν : Measure X) [IsProbabilityMeasure ν]
    (t : Γ → X → ℝ), (∀ γ, Measurable (t γ)) → (∀ γ, ∃ C : ℝ, ∀ x, |t γ x| ≤ C) →
    ∀ u v : X → ℂ, Measurable u → (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) →
      Measurable v → (∃ C : ℝ, ∀ x, ‖v x‖ ≤ C) →
      0 ≤ kernelForm ν t u u ∧
        ‖kernelForm ν t v u‖ ^ 2 ≤ (kernelForm ν t v v).re * (kernelForm ν t u u).re
end YangMills.Construction.ReflectionPositivity.ExpSumProductKernel
end
