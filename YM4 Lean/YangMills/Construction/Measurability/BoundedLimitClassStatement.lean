import Mathlib
set_option autoImplicit false
open Filter Topology
namespace YangMills.Construction.Measurability.BoundedLimitClass
def IsBoundedFn {X : Type} (f : X → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
def IsBoundedMeasurableFn {X : Type} [MeasurableSpace X] (f : X → ℂ) : Prop :=
  Measurable f ∧ IsBoundedFn f
structure IsBoundedLimitClosed {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (𝔉 : Submodule ℂ (X → ℂ)) : Prop where
  boundedMeasurable : ∀ f ∈ 𝔉, IsBoundedMeasurableFn f
  continuous_mem : ∀ f : X → ℂ, Continuous f → IsBoundedFn f → f ∈ 𝔉
  limit_mem : ∀ (u : ℕ → X → ℂ) (f : X → ℂ), (∀ n, u n ∈ 𝔉) → (∃ C : ℝ, ∀ n x, ‖u n x‖ ≤ C) →
    (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) → f ∈ 𝔉
def Claim : Prop :=
  ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (𝔉 : Submodule ℂ (X → ℂ)),
    IsBoundedLimitClosed 𝔉 → (𝔉 : Set (X → ℂ)) = {f | IsBoundedMeasurableFn f}
end YangMills.Construction.Measurability.BoundedLimitClass
