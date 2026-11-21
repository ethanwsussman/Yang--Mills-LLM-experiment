import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses
variable (Tb : ParameterAssignment) (y : ℝ)
def stepCovarianceBoundedAt : Prop :=
  ∃ C : ℝ, ∀ (u n : ℕ) [NeZero n] (h h' : TorusBond (n * (Tb.stepParameters y).side) → ℝ),
    (Tb.stepParameters y).n₀ ≤ n → (Tb.stepParameters y).side ∣ n →
    |stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side u n h h'| ≤ C * (∑ b, |h b|) * ∑ b, |h' b|
def stepCovarianceBoundedStatement : Prop := HoldsOnParameterFamilies stepCovarianceBoundedAt
end YangMills.Construction.ResponseInTheExpansion
end
