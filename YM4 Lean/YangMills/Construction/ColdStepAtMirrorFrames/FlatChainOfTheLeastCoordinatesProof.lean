import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainOfTheLeastCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem flatChain_of_minimizer_coords (h : AxialResponseOfMinimizers) :
    flatChainOfMinimizerCoords := fun a ha =>
  ⟨0, fun L n hL _ hn F c X hFL hF hX => h a ha L hL n hn F c X hFL hF hX⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
