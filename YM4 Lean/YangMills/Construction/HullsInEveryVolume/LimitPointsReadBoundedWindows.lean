import YangMills.Construction.HullsInEveryVolume.LimitDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction
namespace HullsInEveryVolume
open TorusLimits
def windowIntegralConvergenceStatement : Prop :=
  ∀ (L K R : ℕ) (β : ℝ) (ν : Measure (FineField L K)) (ms : ℕ → ℕ) (G : WindowValuation R → ℝ), Odd L → 1 < L → 0 < β →
    IsTorusLimitAlong L K β ν ms → IsBoundedWindowObservable G →
    Tendsto (fun i => ∫ U, evalOnField G U ∂(InfiniteLattice.liftedWilsonMeasure L (ms i) K β)) atTop
      (𝓝 (∫ U, evalOnField G U ∂ν))
end HullsInEveryVolume
end YangMills.Construction
end
