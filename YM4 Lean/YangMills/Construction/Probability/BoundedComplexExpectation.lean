import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Probability
variable {Ω : Type*} [MeasurableSpace Ω]
structure IsBoundedComplexRV (f : Ω → ℂ) : Prop where
  measurable_re : Measurable fun ω => (f ω).re
  measurable_im : Measurable fun ω => (f ω).im
  bounded : ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C
def supModulus (f : Ω → ℂ) : ℝ := ⨆ ω, ‖f ω‖
def complexExpectation (μ : Measure Ω) (f : Ω → ℂ) : ℂ := ∫ ω, f ω ∂μ
end YangMills.Construction.Probability
