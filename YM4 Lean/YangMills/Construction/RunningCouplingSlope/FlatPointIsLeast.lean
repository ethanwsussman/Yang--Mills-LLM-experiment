import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def UnitPointIsMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    RepresentsTorusField (L := L) (n := n) (k := k) (fun _ => 1)
        (TorusFields.trivialField (2 * L ^ n)) ∧
      IsMinimizerOver a (fun _ => 1) (unitPoint L n k)
end RunningCouplingSlope
end YangMills.Construction
end
