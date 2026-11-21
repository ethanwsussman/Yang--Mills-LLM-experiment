import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAboveTheFrameIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem topExpansionContDiffEventually_holds (hj : EventuallyInParametersCombines)
    (hb : CentredExpansionsBounded) : topExpansionContDiffEventually := by
  refine hj.2 _ _ (fun T _ h => ?_) hb
  intro t x f F V hx hf hF hV star Y η hη k c X
  have B := h t x f F V star hx hf hF hV
  have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  unfold cellCentredExpansion
  refine ContDiffAt.sum fun y _ => ?_
  have h1 := B.smooth y η k c X hη'
  have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ((τ, η) : (Fin k → ℝ) × StepVariable (finiteCells F))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have h3 := ContDiffAt.comp (0 : Fin k → ℝ) h1 h2
  exact h3
end YangMills.Construction.ColdStepAtMirrorFrames
end
