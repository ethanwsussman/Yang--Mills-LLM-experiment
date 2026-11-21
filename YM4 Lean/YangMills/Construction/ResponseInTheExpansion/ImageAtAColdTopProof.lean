import YangMills.Construction.ResponseInTheExpansion.ImageAtAColdTop
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings RenormalizationStepParameters StepGas TorusFields BlockAverages
theorem coldImageDecomposition_holds (himage : coldStepIntegralEqGasMean) : coldImageDecompositionStatement := by
  obtain ⟨rt₀, hr, g⟩ := himage
  refine ⟨rt₀, hr, fun T hT hrt K => ?_⟩
  obtain ⟨y₀, g⟩ := g T hT hrt K
  refine ⟨y₀, fun y hy R A hK hA n _ hn Y V hV h => ?_⟩
  have hσ : 0 < R.params.threshold := by
    rw [hA.onFamily.params_eq]
    exact hT.σ_pos
  have hG : (coldCaseGround R V).IsAdmissibleGround := by
    refine Or.inl ⟨hn, fun x μ ν hμ => ?_, rfl, rfl, rfl⟩
    have := hV x μ ν hμ
    show curvature V x μ ν < 9 / 8 * R.params.threshold
    linarith
  have e := (g y hy R A hK hA n (coldCaseGround R V) hG Y h).2
  have e' : A.coldStep n Y V h = _ := e
  rw [e']
  unfold gasBlockMean coldImagePart gasTermAtBlock gasResponseShift gasBondScoreShift
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring
end YangMills.Construction.ResponseInTheExpansion
end
