import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters ColdStepAtMirrorFrames
theorem logIntegralEqSumActivity (hsum : SumActivitiesEqLogIntegral)
    (hreg : DensitySplitRegular) : LogIntegralEqSumActivity := by
  obtain ⟨rt₀, hrt₀, h⟩ := hreg
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨y₁, h1⟩ := h T hT hrt
  refine ⟨max y₁ 1, fun y hy R hR n _ hn s hs => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy2 : (1 : ℝ) ≤ y := (le_max_right _ _).trans hy
  have hx : 0 < R.coupling := by
    have := hR.le_coupling
    linarith
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hthr : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hrad : R.ballRadius = T.ballRadius := by
    unfold StepSettings.StepSetup.ballRadius RenormalizationStepParameters.ParameterAssignment.ballRadius
    rw [hthr]
  have hpos : 0 < R.ballRadius := by
    rw [hrad]
    have := hT.σ_pos
    unfold RenormalizationStepParameters.ParameterAssignment.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    rw [hrad, hR.barrierFn_eq]
    exact hT.cut
  exact hsum R n s.free s.densitySplit T.lam hx hlam hpos hcut (h1 y hy1 R hR n hn s hs)
end YangMills.Construction.ClusterExpansionOfAStep
end
