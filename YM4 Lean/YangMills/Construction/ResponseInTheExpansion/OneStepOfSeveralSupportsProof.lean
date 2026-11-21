import YangMills.Construction.ResponseInTheExpansion.OneStepOfSeveralSupports
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.WeightedResponses
open YangMills.Construction.WeightedObservables
theorem severalSupportsStepDecorrelation_holds (h : severalResponsesStepDecorrelation) :
    severalSupportsStepDecorrelation := by
  obtain ⟨rt₀, hrt₀, H⟩ := h
  refine ⟨rt₀, hrt₀, fun T hT hrt K => ?_⟩
  obtain ⟨y₀, H⟩ := H T hT hrt K
  refine ⟨y₀, fun p => ?_⟩
  obtain ⟨C, H⟩ := H p
  refine ⟨C, fun y hy R A hK htab n _ G hG ι I f D hp hsz hne hr h8 hap => ?_⟩
  exact H y hy R A hK htab ι I (fun _ => A) A.score (fun _ _ => hK) (fun _ _ => rfl) (fun _ _ => htab) n G hG f D
    hp hsz hne hr h8 hap
end YangMills.Construction.ResponseInTheExpansion
end
