import YangMills.Construction.HoleBesideASecondHole.HolesAreFilled
import YangMills.Construction.HoleBesideASecondHole.LegsAndMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleFilling
theorem holesFilled_holds (hMeans : ContourMeans.contourMeansStatement) : holesFilledStatement := by
  intro a ε Θ C J₀ ha hε _ hC hJ
  obtain ⟨CJ, hCJ, h₁⟩ := hMeans a C J₀ ha hC (by omega)
  obtain ⟨L₀, h₂⟩ := h₁ ε hε
  refine ⟨CJ, hCJ, L₀, fun L hL hL₀ g => ?_⟩
  obtain ⟨s₀, hs₀, h₃⟩ := h₂ L hL hL₀ g
  refine ⟨s₀, hs₀, fun s hs hss F D hF hT _ => ?_⟩
  obtain ⟨U, hU⟩ := h₃ s hs hss (Θ * s) F D hF hT
  exact ⟨U, hU.top_eq, hU.energy_le, hU.energy_local_le, hU.eq_fineField_off_lumps⟩
end YangMills.Construction.HoleFilling
end
