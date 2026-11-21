import YangMills.Construction.Probability.BoundedComplexExpectation
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Probability
def ExpectationBasicProperties : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    ((∃ V : Submodule ℝ (Ω → ℝ), (V : Set (Ω → ℝ)) = {f | IsBoundedRealRV f}) ∧
      (∀ c : ℝ, IsBoundedRealRV fun _ : Ω => c) ∧
      (∀ f g : Ω → ℝ, IsBoundedRealRV f → IsBoundedRealRV g →
        IsBoundedRealRV (f * g)) ∧
      (∃ W : Submodule ℂ (Ω → ℂ), (W : Set (Ω → ℂ)) = {F | IsBoundedComplexRV F}) ∧
      (∀ c : ℂ, IsBoundedComplexRV fun _ : Ω => c) ∧
      (∀ F G : Ω → ℂ, IsBoundedComplexRV F → IsBoundedComplexRV G →
        IsBoundedComplexRV (F * G)) ∧
      (∀ f : Ω → ℝ, IsBoundedRealRV f →
        IsBoundedComplexRV fun ω => (f ω : ℂ))) ∧
    ((∀ (F G : Ω → ℂ) (a b : ℂ), IsBoundedComplexRV F →
        IsBoundedComplexRV G →
        complexExpectation μ (a • F + b • G) =
          a * complexExpectation μ F + b * complexExpectation μ G) ∧
      (∀ F : Ω → ℂ, IsBoundedComplexRV F → (∀ ω, (F ω).im = 0) →
        (complexExpectation μ F).im = 0) ∧
      complexExpectation μ (fun _ => 1) = 1 ∧
      (∀ F : Ω → ℂ, IsBoundedComplexRV F →
        ‖complexExpectation μ F‖ ≤ supModulus F)) ∧
    (∀ (f : Ω → ℝ) (c : ℝ), IsBoundedRealRV f → (∀ ω, c ≤ f ω) →
      c ≤ (complexExpectation μ fun ω => (f ω : ℂ)).re) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (f : Fin n → Ω → ℝ) (φ : (Fin n → ℝ) → ℂ),
      (∀ i, IsBoundedRealRV (f i)) → Continuous φ →
        IsBoundedComplexRV (fun ω => φ fun i => f i ω) ∧
        ((∀ t, (φ t).im = 0) →
          IsBoundedRealRV fun ω => (φ fun i => f i ω).re))
end YangMills.Construction.Probability
