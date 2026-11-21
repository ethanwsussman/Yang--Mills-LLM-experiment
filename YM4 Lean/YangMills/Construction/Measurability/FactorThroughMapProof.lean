import YangMills.Construction.Measurability.FactorThroughMapStatement
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Measurability.FactorThroughMap
theorem claim_holds : Claim := by
  intro S Y mY f g hg
  obtain ⟨φ, hφ, hgφ⟩ := hg.exists_eq_measurable_comp
  refine ⟨⟨φ, hφ, hgφ⟩, fun c hc hbound => ?_⟩
  classical
  refine ⟨fun y => if ‖φ y‖ ≤ c then φ y else 0, ?_, ?_, fun y => ?_⟩
  · exact Measurable.ite (measurableSet_le hφ.norm measurable_const) hφ measurable_const
  · funext s
    have hs : ‖φ (f s)‖ ≤ c := by simpa [hgφ] using hbound s
    show g s = if ‖φ (f s)‖ ≤ c then φ (f s) else 0
    rw [if_pos hs, hgφ]
    rfl
  · dsimp only
    split_ifs with hy
    · exact hy
    · simpa using hc
end YangMills.Construction.Measurability.FactorThroughMap
