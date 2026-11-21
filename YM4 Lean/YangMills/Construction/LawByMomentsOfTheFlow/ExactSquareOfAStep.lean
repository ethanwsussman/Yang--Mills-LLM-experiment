import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def completedSquareStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
    ∀ (Y : TorusFields.TorusBond n → ℝ) (η : ChartBondIndex (Tb.stepParameters y).side u n → ℝ),
    WeightedResponses.maxwellForm Tb.coupling (Tb.stepParameters y).side u
        (fun b => WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u Y b + extendChart η b)
        (fun b => WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u Y b + extendChart η b) +
      Tb.coupling * ∑ c : TorusFields.TorusBond n, (contourAverage (Tb.stepParameters y).side
        (fun b => WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u Y b + extendChart η b) c - Y c) ^ 2 =
    WeightedResponses.maxwellForm Tb.coupling (Tb.stepParameters y).side (u + 1) Y Y +
      η ⬝ᵥ ((WeightedResponses.trivialHessian Tb.coupling (Tb.stepParameters y).side u n).mulVec η)
end YangMills.Construction.MomentLaw
end
