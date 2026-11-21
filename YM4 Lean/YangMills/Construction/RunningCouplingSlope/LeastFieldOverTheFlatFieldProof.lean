import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.LeastFieldOverTheFlatField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem minimizerOverTrivialFieldIsTrivial_of_near (h : RunningCouplingSlope.MinimizerNearTrivialField) :
    RunningCouplingSlope.MinimizerOverTrivialFieldIsTrivial := by
  intro a ha L hL t m ρ hm h0 h1
  have hT := (h a ha L hL t (2 * L ^ m) ρ (Nat.mul_le_mul_left 2 (Nat.le_self_pow hm.ne' L)) h0 h1).1
  exact tendsto_nhds_unique (tendsto_pure_nhds _ _) (hT.mono_left (pure_le_nhds _))
end YangMills.Construction.RunningCouplingSlope
end
