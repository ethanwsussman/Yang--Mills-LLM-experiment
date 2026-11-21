import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def MomentConvergenceChargesOpenSets : Prop :=
  ∀ (d : ℕ) (μ : ℕ+ → Measure (Fin d → ℝ)) (ν : Measure (Fin d → ℝ)), (∀ j, IsProbabilityMeasure (μ j)) →
    IsProbabilityMeasure ν → (∃ S : Set (Fin d → ℝ), IsCompact S ∧ ν Sᶜ = 0) →
    (∀ e : Fin d → ℕ, (∀ j, Integrable (fun x => ∏ i, x i ^ e i) (μ j)) ∧
      Tendsto (fun j => ∫ x, ∏ i, x i ^ e i ∂μ j) atTop (𝓝 (∫ x, ∏ i, x i ^ e i ∂ν))) →
    ∀ U : Set (Fin d → ℝ), IsOpen U → 0 < ν U → ∀ᶠ j in atTop, 0 < μ j U
end YangMills.Construction.TotalDensitiesGiveASystem
end
