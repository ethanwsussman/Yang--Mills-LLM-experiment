import YangMills.Construction.HoleBesideASecondHole.CellsKeptOffTheSpots
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open BlockAverages
theorem keptCellsAwayFromBad_of_keptOffBadLumps (h : keptOffBadLumpsStatement) :
    KeptCellsAwayFromBad := by
  intro F L g a s θ C J₀ D hFL hL hc hθ
  obtain ⟨⟨S, hS⟩, hkr, hcold, hall⟩ := h F L g a s θ C J₀ D hFL hL hc hθ
  obtain ⟨hsub, hcore, hreg, hcount⟩ := hall S hS
  refine ⟨hkr, hcold, S, hsub, hreg, fun y hy z hz => ?_, hcount⟩
  exact (Finset.mem_filter.1 (hcore hy)).2 z hz
end YangMills.Construction.HoleSavings
end
