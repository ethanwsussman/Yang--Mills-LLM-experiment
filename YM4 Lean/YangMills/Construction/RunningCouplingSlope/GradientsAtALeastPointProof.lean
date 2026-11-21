import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.GradientsAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.LeastValueAlongATopForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GradientsAtMinimizerProof
open Tower
theorem gradientsAtMinimizer_holds (hgrad : GradientAndMultiplierAtMinimizer)
    (hderiv : MinimalActionDerivAlongTopForm) : GradientsAtMinimizer := by
  intro a ha L hL k n hk hn
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  filter_upwards [hgrad a ha L hL m n hn, hderiv a ha L hL m n hn] with V h1 h2 W hW X hX
  obtain ⟨J, μ, hJ, hM, hB⟩ := h1 W hW X hX
  refine ⟨J, μ, hJ, hM, fun B => ?_⟩
  rw [(h2 W hW X hX B).deriv]
  exact hB B
end YangMills.Construction.RunningCouplingSlope.GradientsAtMinimizerProof
end
