import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem bilinearResponseBound_of_flatResponseSumBounds (h : FlatResponseSumBounds) :
    BilinearResponseBound := h.2.1
end YangMills.Construction.ColdStepAtMirrorFrames
end
