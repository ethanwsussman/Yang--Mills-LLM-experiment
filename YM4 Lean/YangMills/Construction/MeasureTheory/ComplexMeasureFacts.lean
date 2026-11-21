import YangMills.Construction.MeasureTheory.SigmaAdditiveSetFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SetFunctions
variable {X : Type*} [MeasurableSpace X]
def IsBoundedMeasurable (F : X → ℂ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C
def IsFiniteMeasureValues (m : MeasurableSets X → ℝ≥0∞) : Prop :=
  IsFiniteMeasure (toMeasure m) ∧ ∀ A : MeasurableSets X, toMeasure m (A : Set X) = m A
def IsFiniteNonnegMeasure (m : MeasurableSets X → ℂ) : Prop :=
  IsCountablyAdditive m ∧ IsNonneg m ∧ IsFiniteMeasureValues fun A => ENNReal.ofReal (m A).re
def VariationReImFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ ν : MeasurableSets X → ℂ, IsCountablyAdditive ν →
    IsFiniteMeasureValues (variation ν) ∧
    (∀ A, ‖ν A‖ₑ ≤ variation ν A) ∧
    IsCountablyAdditive (reFn ν) ∧ IsCountablyAdditive (imFn ν) ∧
    (∀ A, variation (reFn ν) A ≤ variation ν A) ∧
    (∀ A, variation (imFn ν) A ≤ variation ν A)
def JordanDecompositionFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ μ : MeasurableSets X → ℂ, IsCountablyAdditive μ → (∀ A, (μ A).im = 0) →
    IsFiniteNonnegMeasure (posPart μ) ∧
    IsFiniteNonnegMeasure (negPart μ) ∧
    (∀ A, ENNReal.ofReal (posPart μ A).re ≤ variation μ A) ∧
    (∀ A, ENNReal.ofReal (negPart μ A).re ≤ variation μ A) ∧
    ∀ A, μ A = posPart μ A - negPart μ A
def NonnegMeasureFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ ν : MeasurableSets X → ℂ, IsCountablyAdditive ν → IsNonneg ν →
    IsFiniteNonnegMeasure ν ∧
    (∀ A, variation ν A = ENNReal.ofReal (ν A).re) ∧
    ∀ F : X → ℂ, IsBoundedMeasurable F →
      integralWith ν F = ∫ x, F x ∂(nonnegToMeasure ν)
def IntegralWithFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ ν : MeasurableSets X → ℂ, IsCountablyAdditive ν →
    (∀ F G : X → ℂ, IsBoundedMeasurable F → IsBoundedMeasurable G →
      integralWith ν (F + G) = integralWith ν F + integralWith ν G) ∧
    (∀ (c : ℂ) (F : X → ℂ), IsBoundedMeasurable F →
      integralWith ν (c • F) = c * integralWith ν F) ∧
    (∀ A : MeasurableSets X, integralWith ν ((A : Set X).indicator fun _ => 1) = ν A) ∧
    ∀ F : X → ℂ, IsBoundedMeasurable F →
      ‖integralWith ν F‖ ≤ ∫ x, ‖F x‖ ∂(toMeasure (variation ν)) ∧
      ∫ x, ‖F x‖ ∂(toMeasure (variation ν)) ≤
        (⨆ x, ‖F x‖) * (variation ν ⟨Set.univ, MeasurableSet.univ⟩).toReal
def AddSMulFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ (ν ν' : MeasurableSets X → ℂ) (c : ℂ), IsCountablyAdditive ν → IsCountablyAdditive ν' →
    IsCountablyAdditive (ν + ν') ∧ IsCountablyAdditive (c • ν) ∧
    (∀ A, variation (ν + ν') A ≤ variation ν A + variation ν' A) ∧
    (∀ A, variation (c • ν) A = ‖c‖ₑ * variation ν A) ∧
    ∀ F : X → ℂ, IsBoundedMeasurable F →
      integralWith (ν + ν') F = integralWith ν F + integralWith ν' F ∧
      integralWith (c • ν) F = c * integralWith ν F
def BoundedConvergenceFacts (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ (ν : MeasurableSets X → ℂ) (F : X → ℂ) (Fs : ℕ → X → ℂ), IsCountablyAdditive ν →
    IsBoundedMeasurable F → (∀ j, 1 ≤ j → IsBoundedMeasurable (Fs j)) →
    (∃ C : ℝ, ∀ j, 1 ≤ j → ∀ x, ‖Fs j x‖ ≤ C) →
    (∀ x, Tendsto (fun j => Fs j x) atTop (𝓝 (F x))) →
    Tendsto (fun j => integralWith ν (Fs j)) atTop (𝓝 (integralWith ν F))
def ComplexMeasureFacts : Prop :=
  ∀ (X : Type) [MeasurableSpace X],
    VariationReImFacts X ∧ JordanDecompositionFacts X ∧
    NonnegMeasureFacts X ∧ IntegralWithFacts X ∧
    AddSMulFacts X ∧ BoundedConvergenceFacts X
end YangMills.Construction.SetFunctions
