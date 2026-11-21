import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures.Pushforward
noncomputable def pushforward {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → Y) (_hT : Measurable T) : Measure Y :=
  μ.map T
theorem pushforward_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → Y) (hT : Measurable T) {A : Set Y} (hA : MeasurableSet A) :
    pushforward μ T hT A = μ (T ⁻¹' A) :=
  Measure.map_apply hT hA
def IsInvariant {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (_hT : Measurable T) : Prop :=
  ∀ A : Set X, MeasurableSet A → μ (T ⁻¹' A) = μ A
theorem isInvariant_iff_pushforward_eq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) :
    IsInvariant μ T hT ↔ pushforward μ T hT = μ := by
  constructor
  · intro h
    ext A hA
    rw [pushforward_apply μ T hT hA]
    exact h A hA
  · intro h A hA
    rw [← pushforward_apply μ T hT hA, h]
def vectorOf {Ω : Type*} {n : ℕ} (Z : Fin n → Ω → ℂ) : Ω → Fin n → ℂ :=
  fun ω i => Z i ω
noncomputable def jointDistribution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (Z : Fin n → Ω → ℂ) (hZ : ∀ i, Measurable (Z i)) :
    Measure (Fin n → ℂ) :=
  pushforward P (vectorOf Z) (measurable_pi_lambda _ hZ)
end YangMills.Construction.Measures.Pushforward
