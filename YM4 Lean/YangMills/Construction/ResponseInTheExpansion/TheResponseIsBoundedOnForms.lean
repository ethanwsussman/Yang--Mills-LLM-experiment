import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters
def responseKernelRowSumBoundedStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∃ C₂ : ℝ, ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
    ∀ b : TorusBond (n * (Tb.stepParameters y).side),
      ∑ c : TorusBond n, |responseKernel Tb.coupling Tb.ρA (Tb.stepParameters y).side u b c| ≤ C₂
end YangMills.Construction.ResponseInTheExpansion
end
