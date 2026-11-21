import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
theorem multilinearResponseBound_holds (h : ColdStepAtMirrorFrames.FlatResponseSumBounds) :
    multilinearResponseBound := h.1
end YangMills.Construction.Interpolation
end
