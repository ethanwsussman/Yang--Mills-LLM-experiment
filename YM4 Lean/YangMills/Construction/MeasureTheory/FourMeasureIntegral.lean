import YangMills.Construction.MeasureTheory.SigmaAdditiveSetFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.BorelComplexMeasures
open YangMills.Construction.SetFunctions
variable {X : Type*} [MeasurableSpace X]
def IsJordanCombination (ν : MeasurableSets X → ℂ) (ν₁ ν₂ ν₃ ν₄ : Measure X) : Prop :=
  IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ IsFiniteMeasure ν₃ ∧ IsFiniteMeasure ν₄ ∧
    ∀ Δ : MeasurableSets X, ν Δ = ((ν₁.real Δ - ν₂.real Δ : ℝ) : ℂ) +
      Complex.I * ((ν₃.real Δ - ν₄.real Δ : ℝ) : ℂ)
def combinedIntegral (ν₁ ν₂ ν₃ ν₄ : Measure X) (g : X → ℂ) : ℂ :=
  ∫ x, g x ∂ν₁ - ∫ x, g x ∂ν₂ + Complex.I * ∫ x, g x ∂ν₃ - Complex.I * ∫ x, g x ∂ν₄
def IsIntegralOf (ν : MeasurableSets X → ℂ) (g : X → ℂ) (c : ℂ) : Prop :=
  ∃ ν₁ ν₂ ν₃ ν₄ : Measure X, IsJordanCombination ν ν₁ ν₂ ν₃ ν₄ ∧ Measurable g ∧
    Integrable g ν₁ ∧ Integrable g ν₂ ∧ Integrable g ν₃ ∧ Integrable g ν₄ ∧
      c = combinedIntegral ν₁ ν₂ ν₃ ν₄ g
def integralOf (ν : MeasurableSets X → ℂ) (g : X → ℂ) : ℂ :=
  Classical.epsilon (IsIntegralOf ν g)
def conjMeasure (ν : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun Δ => (starRingEnd ℂ) (ν Δ)
def densityMul (g : X → ℂ) (ν : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun Δ => integralOf ν fun x => (Δ : Set X).indicator (fun _ => (1 : ℂ)) x * g x
end YangMills.Construction.BorelComplexMeasures
