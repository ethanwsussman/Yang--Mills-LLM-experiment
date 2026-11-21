import YangMills.Construction.EuclideanAnalysis.RadialCutOffAndContinuousDensities
import YangMills.Construction.EuclideanAnalysis.RadialCutOffHasItsProperties
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanAnalysis.CubedLaplacian
theorem radialBumpHasProperties_holds (h : BumpAndDensities.Combined) :
    RadialBumpHasProperties := by
  obtain ⟨⟨χ, hradial, hvalues, hone⟩, -, -⟩ := h
  have hexists : ∃ ψ : CompactSupportClass ⊤ unitBallOpens ℝ, IsRadialBump ψ := by
    refine ⟨χ, hradial, hvalues, ?_⟩
    filter_upwards [Metric.closedBall_mem_nhds (0 : RealSpace 4) (by norm_num : (0 : ℝ) < 1 / 2)]
      with x hx
    exact hone x (by simpa using hx)
  have : Nonempty (CompactSupportClass ⊤ unitBallOpens ℝ) := ⟨0⟩
  exact Classical.epsilon_spec hexists
end YangMills.Construction.EuclideanAnalysis.CubedLaplacian
