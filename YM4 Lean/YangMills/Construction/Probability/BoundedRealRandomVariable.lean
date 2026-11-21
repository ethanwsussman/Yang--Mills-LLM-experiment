import Mathlib
namespace YangMills.Construction
namespace Probability
variable {Ω : Type*} [MeasurableSpace Ω]
structure IsBoundedRealRV (x : Ω → ℝ) : Prop where
  measurable : Measurable x
  bounded : ∃ C : ℝ, ∀ ω, |x ω| ≤ C
end Probability
end YangMills.Construction
