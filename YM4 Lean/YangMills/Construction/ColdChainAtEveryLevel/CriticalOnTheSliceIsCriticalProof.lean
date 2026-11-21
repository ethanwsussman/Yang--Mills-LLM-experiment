import YangMills.Construction.ColdChainAtEveryLevel.CriticalAlongTheSliceUnderAnyTop
import YangMills.Construction.ColdChainAtEveryLevel.CriticalOnTheSliceIsCritical
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
theorem criticalOnSlice_of_sliceCriticalImpliesCritical (h : sliceCriticalImpliesCriticalStatement) :
    criticalOnSliceStatement := by
  intro a δ ha hδ hδ8
  obtain ⟨L₀, hL⟩ := h a δ ha hδ hδ8
  refine ⟨L₀, fun L hodd hge => ?_⟩
  obtain ⟨c, hc, h'⟩ := hL L hodd hge
  exact ⟨c, hc, fun F m S hF hamb hm hreg s V hs hsc hcold U hU hcrit =>
    h' F m S hF hamb hm hreg s V V hs hsc hcold U hU hcrit⟩
end YangMills.Construction.BlockAverages
end
