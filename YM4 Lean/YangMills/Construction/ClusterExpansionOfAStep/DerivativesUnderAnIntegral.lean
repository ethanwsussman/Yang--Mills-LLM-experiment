import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ParametricIntegral
def ContDiffOnIntegralStatement : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (k N : ℕ) (U : Set (Fin k → ℝ)) (F : α → (Fin k → ℝ) → ℝ)
    (g : α → ℝ), IsOpen U → Integrable g μ → (∀ a, ContDiffOn ℝ N (F a) U) →
    (∀ x ∈ U, AEStronglyMeasurable (fun a => F a x) μ) →
    (∀ a, ∀ j ≤ N, ∀ x ∈ U, ‖iteratedFDeriv ℝ j (F a) x‖ ≤ g a) →
    ContDiffOn ℝ N (fun x => ∫ a, F a x ∂μ) U ∧
      ∀ j ≤ N, ∀ x ∈ U, ∀ h : α → ℝ, Integrable h μ → (∀ a, ‖iteratedFDeriv ℝ j (F a) x‖ ≤ h a) →
        ‖iteratedFDeriv ℝ j (fun x => ∫ a, F a x ∂μ) x‖ ≤ ∫ a, h a ∂μ
end YangMills.Construction.ParametricIntegral
end
