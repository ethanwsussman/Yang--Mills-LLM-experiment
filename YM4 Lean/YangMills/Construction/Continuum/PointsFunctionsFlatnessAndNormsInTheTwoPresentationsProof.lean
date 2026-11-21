import YangMills.Construction.Continuum.PointsFunctionsFlatnessAndNormsInTheTwoPresentations
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.TwoPresentations
theorem presentationsAgree_holds : PresentationsAgree := by
  intro n
  have hSchwartz : ∀ φ : TestSpaces.PointTuple n → ℂ,
      ConfigSpace.IsSchwartz φ ↔ φ ∈ TestSpaces.schwartzSet n :=
    fun φ => ⟨fun h => ⟨h.1, fun k hk => h.2 k hk⟩, fun h => ⟨h.1, fun k hk => h.2 k hk⟩⟩
  have hFlat : ∀ (φ : TestSpaces.PointTuple n → ℂ) (x : TestSpaces.PointTuple n),
      ConfigSpace.FlatAt φ x ↔ TestSpaces.VanishesToInfiniteOrderAt φ x :=
    fun φ x => ⟨fun h => ⟨h.1, h.eq_zero, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, hSchwartz, ?_,
    hFlat, ?_, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  · ext φ
    exact ConfigSpace.isSchwartz_iff_mem_schwartzSpace.symm.trans (hSchwartz φ)
  · intro φ V
    exact ⟨fun h => ⟨h.1, h.2.1, fun x hx => (hFlat φ x).1 (h.2.2 x hx)⟩,
      fun h => ⟨h.1, h.2.1, fun x hx => (hFlat φ x).2 (h.2.2 x hx)⟩⟩
  · intro k φ
    have hlt : ConfigSpace.schwartzSeminorm k φ.1 < ⊤ :=
      (ConfigSpace.isSchwartz_iff_mem_schwartzSpace.1 φ.2).2 k
    exact ENNReal.ofReal_toReal hlt.ne
end YangMills.Construction.Continuum.TwoPresentations
end
