import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
namespace LatticeForms
section MoorePenrose
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def orthProj (W : Submodule ℝ V) : V →ₗ[ℝ] V := (W.starProjection : V →L[ℝ] V)
omit [FiniteDimensional ℝ V] in
theorem orthogonal_range_eq_ker {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) :
    (LinearMap.range T)ᗮ = LinearMap.ker T :=
  hT.orthogonal_range
theorem isCompl_range_ker {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) :
    IsCompl (LinearMap.range T) (LinearMap.ker T) := by
  rw [← orthogonal_range_eq_ker hT]
  exact Submodule.isCompl_orthogonal _
def restrictToRange (T : V →ₗ[ℝ] V) : LinearMap.range T →ₗ[ℝ] LinearMap.range T :=
  T.restrict fun v _ => LinearMap.mem_range_self T v
theorem restrictToRange_injective {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) :
    Function.Injective (restrictToRange T) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  have hk : (w : V) ∈ LinearMap.ker T := by
    have := congrArg Subtype.val hw
    simpa [restrictToRange] using this
  have := Submodule.disjoint_def.mp (isCompl_range_ker hT).disjoint (w : V) w.2 hk
  exact Subtype.ext this
open Classical in
def moorePenrose (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  if hT : T.IsPositive then
    (LinearMap.range T).subtype ∘ₗ
      ((LinearEquiv.ofInjectiveEndo (restrictToRange T)
        (restrictToRange_injective hT.isSymmetric)).symm : _ →ₗ[ℝ] _) ∘ₗ
      ((LinearMap.range T).orthogonalProjectionOnto : V →ₗ[ℝ] LinearMap.range T)
  else 0
variable {T : V →ₗ[ℝ] V}
theorem moorePenrose_mem_range (hT : T.IsPositive) (v : V) :
    moorePenrose T v ∈ LinearMap.range T := by
  simp only [moorePenrose, dif_pos hT]
  exact Subtype.coe_prop _
theorem apply_moorePenrose (hT : T.IsPositive) (v : V) :
    T (moorePenrose T v) = orthProj (LinearMap.range T) v := by
  simp only [moorePenrose, dif_pos hT]
  have hinj := restrictToRange_injective hT.isSymmetric
  have h := (congrFun (LinearEquiv.coe_ofInjectiveEndo (restrictToRange T) hinj)
    ((LinearEquiv.ofInjectiveEndo (restrictToRange T) hinj).symm
      ((LinearMap.range T).orthogonalProjectionOnto v))).symm.trans
    (LinearEquiv.apply_symm_apply (LinearEquiv.ofInjectiveEndo (restrictToRange T) hinj)
      ((LinearMap.range T).orthogonalProjectionOnto v))
  exact congrArg Subtype.val h
theorem moorePenrose_apply_of_mem_ker (hT : T.IsPositive) {v : V} (hv : v ∈ LinearMap.ker T) :
    moorePenrose T v = 0 := by
  have h₀ : (LinearMap.range T).orthogonalProjectionOnto v = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, orthogonal_range_eq_ker hT.isSymmetric]
    exact hv
  simp only [moorePenrose, dif_pos hT]
  simp [h₀]
theorem eq_of_apply_eq_of_mem_range (hT : T.IsPositive) {u v : V} (hu : u ∈ LinearMap.range T)
    (hv : v ∈ LinearMap.range T) (h : T u = T v) : u = v := by
  have := restrictToRange_injective hT.isSymmetric (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩)
    (Subtype.ext h)
  exact congrArg Subtype.val this
theorem orthProj_apply_of_mem {W : Submodule ℝ V} {v : V} (hv : v ∈ W) :
    orthProj W v = v :=
  Submodule.starProjection_eq_self_iff.mpr hv
theorem moorePenrose_apply_apply_of_mem (hT : T.IsPositive) {v : V}
    (hv : v ∈ LinearMap.range T) : moorePenrose T (T v) = v :=
  eq_of_apply_eq_of_mem_range hT (moorePenrose_mem_range hT _) hv (by
    rw [apply_moorePenrose hT, orthProj_apply_of_mem (LinearMap.mem_range_self T v)])
end MoorePenrose
end LatticeForms
end
end YangMills.Construction
