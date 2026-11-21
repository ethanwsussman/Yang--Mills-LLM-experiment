import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures.MomentDetermination
def measureSupport {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) : Set X :=
  {x | ∀ U : Set X, IsOpen U → x ∈ U → 0 < μ U}
def mixedMoments_determine : Prop :=
  ∀ (Y X₁ X₂ : Type)
    [TopologicalSpace X₁] [CompactSpace X₁] [TopologicalSpace.MetrizableSpace X₁]
    [MeasurableSpace X₁] [BorelSpace X₁]
    [TopologicalSpace X₂] [CompactSpace X₂] [TopologicalSpace.MetrizableSpace X₂]
    [MeasurableSpace X₂] [BorelSpace X₂]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (φ₁ : Y → X₁ → ℝ) (φ₂ : Y → X₂ → ℝ),
    IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
    measureSupport μ₁ = Set.univ → measureSupport μ₂ = Set.univ →
    (∀ y, Continuous (φ₁ y)) → (∀ y, Continuous (φ₂ y)) →
    (∀ a b : X₁, a ≠ b → ∃ y, φ₁ y a ≠ φ₁ y b) →
    (∀ a b : X₂, a ≠ b → ∃ y, φ₂ y a ≠ φ₂ y b) →
    (∀ q : ℕ, 1 ≤ q → ∀ t : Fin q → Y,
      ∫ x, ∏ i, φ₁ (t i) x ∂μ₁ = ∫ x, ∏ i, φ₂ (t i) x ∂μ₂) →
    ∃ h : X₁ → X₂, (∀ y, φ₂ y ∘ h = φ₁ y) ∧
      (∀ k : X₁ → X₂, (∀ y, φ₂ y ∘ k = φ₁ y) → k = h) ∧
      IsHomeomorph h ∧ Measure.map h μ₁ = μ₂
end YangMills.Construction.Measures.MomentDetermination
