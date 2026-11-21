import YangMills.Construction.ReflectionPositivity.HyperplanesOfATorusMirrorAreOfOneKind
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorLevelKinds
private theorem mesh_ne_zero (D : MirrorData) : D.mesh ≠ 0 := by
  have hL : (0 : ℝ) < D.L := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  simp only [MirrorData.mesh, PeriodicLattice.meshSize]
  exact (zpow_pos hL _).ne'
private theorem half_side_eq (D : MirrorData) : D.side / 2 = (D.halfSideCount : ℝ) * D.mesh := by
  have hm := mesh_ne_zero D
  have h := D.side_div_mesh
  field_simp at h
  linarith
private theorem siteLevels_add_half_side (D : MirrorData) (c : ℝ) :
    c ∈ siteLevels D.mesh ↔ c + D.side / 2 ∈ siteLevels D.mesh := by
  rw [half_side_eq]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q + D.halfSideCount, by push_cast; ring⟩
  · rintro ⟨q, hq⟩
    exact ⟨q - D.halfSideCount, by push_cast; linarith⟩
private theorem linkLevels_add_half_side (D : MirrorData) (c : ℝ) :
    c ∈ linkLevels D.mesh ↔ c + D.side / 2 ∈ linkLevels D.mesh := by
  rw [half_side_eq]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q + D.halfSideCount, by push_cast; ring⟩
  · rintro ⟨q, hq⟩
    exact ⟨q - D.halfSideCount, by push_cast; linarith⟩
theorem statement_holds : Statement := by
  intro D
  refine ⟨?_, fun c => ⟨siteLevels_add_half_side D c, linkLevels_add_half_side D c⟩,
    fun μ c hc => ⟨⟨rfl, rfl, ?_⟩, ?_⟩⟩
  · have h := half_side_eq D
    unfold HalfSideOverMesh
    rw [div_eq_iff (mul_ne_zero two_ne_zero (mesh_ne_zero D))]
    linarith
  · exact image_union _ _ _
  · rw [halfLevels_eq_union] at hc
    rcases hc with hc | hc
    · exact Or.inl ⟨hc, (siteLevels_add_half_side D c).1 hc⟩
    · exact Or.inr ⟨hc, (linkLevels_add_half_side D c).1 hc⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorLevelKinds
