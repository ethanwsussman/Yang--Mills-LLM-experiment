import YangMills.Construction.NormedSpaces.UniformBoundMultilinearForms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces.MultilinearUniformBound
open BanachSteinhaus
theorem uniformBoundednessPrinciple_of_banachSteinhaus
    (hBS : BanachSteinhaus.linearAndMultilinear) :
    uniformBoundednessPrinciple := by
  intro J k hk E _ _ _ T hbdd hpt
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have hvac : ∀ C : ℝ, IsUniformFormBound T C := fun _ j => (hJ.false j).elim
    refine ⟨⟨0, hvac 0⟩, ?_, hvac _⟩
    rw [Set.range_eq_empty]
    exact bddAbove_empty
  · obtain ⟨hsup, hC⟩ := hBS.2 J k hk E T hbdd hpt
    exact ⟨⟨_, hC⟩, hsup, hC⟩
end YangMills.Construction.NormedSpaces.MultilinearUniformBound
