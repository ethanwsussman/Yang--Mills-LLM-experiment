import YangMills.Construction.Continuum.ExtensionToTheSchwartzFunctionsFlatOnTheDiagonals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.FlatSchwartzExtension
theorem uniqueBoundedExtension_of_flatExtension
    (hExt : FlatExtension.FlatExtensionClaim) : UniqueBoundedExtension := by
  intro n c a G T hn hc hG hT
  obtain ⟨hUniq, hBd, hFact⟩ := hExt n c a G T hn hc hG hT
  exact ⟨hUniq, fun S hS => hBd S hS, hFact⟩
end YangMills.Construction.FlatSchwartzExtension
