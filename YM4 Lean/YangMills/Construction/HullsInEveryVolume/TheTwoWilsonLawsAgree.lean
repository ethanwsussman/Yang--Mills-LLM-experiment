import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.HullsInEveryVolume
open WeightedResponses TorusLimits
def wilsonLawsAgreeStatement : Prop :=
  ∀ (L K m R : ℕ) [NeZero L] (β : ℝ) (G : WindowValuation R → ℝ), Odd L → 1 < L → 0 < m → 0 < β →
    IsBoundedWindowObservable G →
    ∫ W, evalOnTorus G W ∂(wilsonLaw β (fineSide L K (2 * L ^ m))) =
      ∫ U, evalOnField G U ∂(InfiniteLattice.liftedWilsonMeasure L m K β)
end YangMills.Construction.HullsInEveryVolume
end
