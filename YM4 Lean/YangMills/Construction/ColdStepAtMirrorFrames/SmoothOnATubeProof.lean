import YangMills.Construction.ColdStepAtMirrorFrames.SmoothNearACompactSet
import YangMills.Construction.ColdStepAtMirrorFrames.SmoothOnATube
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem uniformDerivBoundNearCompact_holds (h : UniformDerivBoundNearCompactOfContinuous) :
    UniformDerivBoundNearCompact := by
  intro k Q _ _ G K hK hG
  obtain ⟨r, M, hr, -, hs⟩ := h k Q G K hK hG
  exact ⟨r, M, hr, hs⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
