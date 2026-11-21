import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.MomentLaw
def minimizerCurveStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
    ∀ B : TorusFields.TorusBond n → ℝ,
    ∃ γ : ℝ → TorusFields.TorusBond (n * T.side) → ℝ, ContDiffAt ℝ 2 γ 0 ∧ γ 0 = 0 ∧
      deriv γ 0 = WeightedResponses.responseMap T.coupling T.ρA T.side u B ∧
      ∀ᶠ τ in 𝓝 (0 : ℝ), ClusterExpansionOfAStep.minimizingField T.coupling T.ρA T.side u Finset.univ
        (ResponseInTheExpansion.expOfColourForm τ B) = ResponseInTheExpansion.expOfColourForm 1 (γ τ)
end YangMills.Construction.MomentLaw
end
