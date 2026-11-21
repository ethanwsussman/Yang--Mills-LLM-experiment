import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
def agingIndex : ℕ := 2 * 16 ^ 2
def agingEntropyConst : ℝ := 3 ^ 4 * 2 ^ 5
def agingPrecision : ℝ := (2 * agingEntropyConst) ^ (-(agingIndex : ℤ))
def AnchorPrecisionIsAgingPrecision (N : ExternalConstants) : Prop :=
  N.εStar = agingPrecision
end YangMills.Construction.ParameterChoice
end
