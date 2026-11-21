import YangMills.Construction.ColdChainAtEveryLevel.ExcessOverTheCriticalChain
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.BlockAverages
theorem criticalChainMinimality_of_excess (h : criticalChainExcessStatement) :
    criticalChainMinimalityStatement := by
  intro a θ del Ca ha hθ hθ₈ hdel hdel₈ hCa
  obtain ⟨L₀, hL⟩ := h a θ del Ca ha hθ hθ₈ hdel hdel₈ hCa
  refine ⟨L₀, fun L hodd hle C₁ hC₁ => ?_⟩
  obtain ⟨C, hC, e0, σ, c, he0, hσ, hc, hmain⟩ := hL L hodd hle C₁ hC₁
  exact ⟨e0, σ, C, c, he0, hσ, hC, hc, hmain⟩
end YangMills.Construction.BlockAverages
