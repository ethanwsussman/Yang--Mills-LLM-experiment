import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLimits
def limitAlongSidesMemTorusLimitSetStatement : Prop :=
  ∀ (L K : ℕ) (β : ℝ) (ν : Measure (FineField L K)) (ms : ℕ → ℕ), Odd L → 1 < L → 0 < β →
    IsTorusLimitAlong L K β ν ms → ν ∈ InfiniteLattice.torusLimitSet L K β
end YangMills.Construction.TorusLimits
end
