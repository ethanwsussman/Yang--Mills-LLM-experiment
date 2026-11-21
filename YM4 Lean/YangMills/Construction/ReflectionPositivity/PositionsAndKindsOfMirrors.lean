import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
def siteLevels (a : ℝ) : Set ℝ := {c | ∃ q : ℤ, c = (q : ℝ) * a}
def linkLevels (a : ℝ) : Set ℝ := {c | ∃ q : ℤ, c = ((q : ℝ) + 1 / 2) * a}
def halfLevels (a : ℝ) : Set ℝ := {c | ∃ q : ℤ, c = (q : ℝ) * (a / 2)}
theorem halfLevels_eq_union (a : ℝ) :
    halfLevels a = siteLevels a ∪ linkLevels a := by
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    rcases Int.even_or_odd' q with ⟨k, rfl | rfl⟩
    · exact Or.inl ⟨k, by push_cast; ring⟩
    · exact Or.inr ⟨k, by push_cast; ring⟩
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨2 * q, by push_cast; ring⟩
    · exact ⟨2 * q + 1, by push_cast; ring⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror
