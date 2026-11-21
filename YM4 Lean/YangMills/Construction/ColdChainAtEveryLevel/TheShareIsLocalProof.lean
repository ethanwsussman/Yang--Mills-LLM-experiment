import YangMills.Construction.ColdChainAtEveryLevel.TheShareIsLocal
import YangMills.Construction.ColdChainAtEveryLevel.TheShareNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockAverages
theorem shareLocalityStatement_of_cell (h : cellShareIsLocalStatement) :
    shareLocalityStatement := by
  classical
  intro a ha
  obtain ⟨L₀, h₁⟩ := h a ha
  refine ⟨L₀, fun L hL hge => ?_⟩
  obtain ⟨c, Ck, hc, hCk, h₂⟩ := h₁ L hL hge
  refine ⟨c, Ck, hc, hCk, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU Y
  exact h₂ F m S hFL hamb hm hreg s V hs hsc hcold U Y (topBondsMeetingCell S Y)
    (fun b => by simp [topBondsMeetingCell, Finset.mem_filter]) (fun hY => hU Y hY)
end YangMills.Construction.BlockAverages
end
