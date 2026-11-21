import YangMills.Construction.RunningCouplingSlope.LeastFieldIsOneOnLargeTori
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem minimizerUniqueUpToGauge_of_near (hnear : MinimizerNearTrivialField) : MinimizerUniqueUpToGauge := by
  intro a ha L hL t ρ h0 h1
  filter_upwards [eventually_ge_atTop (2 * L)] with n hn
  filter_upwards [(hnear a ha L hL t n ρ hn h0 h1).2] with V hV
  exact ⟨hV.1, fun W hW => hV.2.1 W hW⟩
end YangMills.Construction.RunningCouplingSlope
end
