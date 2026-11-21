import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedGreen
def coercivityConst (lowerWeight : ℝ) : ℝ := min 4 lowerWeight
def expDecayRate (dim blockFactor : ℕ) (lowerWeight upperWeight : ℝ) : ℝ :=
  coercivityConst lowerWeight / (8 * (dim : ℝ) * ((blockFactor : ℝ) ^ 2 + upperWeight))
end WeightedGreen
end YangMills.Construction
