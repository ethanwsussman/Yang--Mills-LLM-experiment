import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def IsExtremeState (S : Set (Measure (GaugeField a))) (μ : Measure (GaugeField a)) :
    Prop :=
  μ ∈ S ∧ ∀ μ₁ ∈ S, ∀ μ₂ ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
    μ = ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂ → μ₁ = μ ∧ μ₂ = μ
end YangMills.Construction.InfiniteLattice
