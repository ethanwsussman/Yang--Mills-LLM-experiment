import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
theorem twoGaugedResponseSumBound_of_flatResponseSumBounds
    (h : ColdStepAtMirrorFrames.FlatResponseSumBounds) :
    TwoGaugedResponseSumBound := h.2.2
end YangMills.Construction.WeightedResponses
end
