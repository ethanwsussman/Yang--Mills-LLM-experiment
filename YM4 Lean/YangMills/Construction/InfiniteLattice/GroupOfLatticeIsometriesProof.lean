import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometries
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {a : ℝ}
theorem euclidNormVec_hyperoctahedral {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) (x : AmbientSpace) :
    euclidNormVec (w x) = euclidNormVec x := by
  obtain ⟨π, s, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
  unfold TorusMetric.euclidNormVec
  congr 1
  calc ∑ μ, (w x) μ ^ 2 = ∑ μ, x (π μ) ^ 2 := Finset.sum_congr rfl fun μ _ => by
        rw [h x μ]
        rcases Int.units_eq_one_or (s μ) with e | e <;> simp [e]
    _ = ∑ μ, x μ ^ 2 := Equiv.sum_comp π fun μ => x μ ^ 2
theorem hyperoctahedral_mem_latticeSubgroup {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) {x : AmbientSpace}
    (hx : x ∈ latticeSubgroup a) : w x ∈ latticeSubgroup a := by
  obtain ⟨π, s, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
  obtain ⟨n, hn⟩ := hx
  refine ⟨fun μ => (s μ : ℤ) * n (π μ), fun μ => ?_⟩
  rw [h x μ, hn]
  push_cast
  ring
theorem eq_zero_of_euclidNormVec_eq_zero {x : AmbientSpace} (h : euclidNormVec x = 0) :
    x = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem signedUnitVectors_finite : signedUnitVectors.Finite := by
  refine (Set.finite_range fun p : Fin 4 × Bool =>
    (if p.2 then Pi.single p.1 1 else -Pi.single p.1 1 : AmbientSpace)).subset ?_
  rintro x ⟨μ, rfl | rfl⟩
  · exact ⟨(μ, true), by simp⟩
  · exact ⟨(μ, false), by simp⟩
theorem exists_affine_of_latticeIsometry
    (hI : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (ha : 0 < a) (r : AmbientSpace → AmbientSpace)
    (hd : ∀ x y, euclidNormVec (r x - r y) = euclidNormVec (x - y))
    (ho : r '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a) :
    ∃ w ∈ hyperoctahedralLinearGroup, ∃ v : LatticePoint a, ∀ x, r x = w x + v := by
  obtain ⟨R, -, v₀, hR⟩ := hI r hd
  have h0 : r 0 = v₀ := by simpa using hR 0
  have hsite : ∀ x ∈ latticeSubgroup a, r x ∈ latticeSubgroup a := fun x hx => by
    have h1 : r x ∈ r '' (latticeSubgroup a : Set AmbientSpace) := Set.mem_image_of_mem r hx
    rwa [ho] at h1
  have hv : v₀ ∈ latticeSubgroup a := h0 ▸ hsite 0 (zero_mem _)
  let f : AmbientSpace →ₗ[ℝ] AmbientSpace := Matrix.mulVecLin R
  have hf : ∀ x, f x = r x - v₀ := fun x => by
    rw [hR x, add_sub_cancel_right]
    rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : r x = r y := by
      rw [hf, hf] at hxy
      exact sub_left_injective hxy
    have h2 := hd x y
    rw [h1, sub_self] at h2
    have h3 : euclidNormVec (0 : AmbientSpace) = 0 := by simp [TorusMetric.euclidNormVec]
    rw [h3] at h2
    exact sub_eq_zero.mp (eq_zero_of_euclidNormVec_eq_zero h2.symm)
  have hbasis : ∀ μ : Fin 4, f (Pi.single μ 1) ∈ signedUnitVectors := by
    intro μ
    obtain ⟨m, hm⟩ := hsite _ (axisStep a μ).2
    obtain ⟨k, hk⟩ := hv
    have hstep : ((axisStep a μ : LatticePoint a) : AmbientSpace) =
        a • (Pi.single μ 1 : AmbientSpace) := by
      funext ν
      by_cases h : ν = μ
      · subst h
        simp [axisStep]
      · simp [axisStep, Pi.single_eq_of_ne h]
    have hint : ∀ ν, f (Pi.single μ 1) ν = ((m ν - k ν : ℤ) : ℝ) := by
      intro ν
      have h1 : f ((axisStep a μ : LatticePoint a) : AmbientSpace) ν =
          ((m ν - k ν : ℤ) : ℝ) * a := by
        rw [hf, Pi.sub_apply, hm, hk]
        push_cast
        ring
      rw [hstep, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm] at h1
      exact mul_right_cancel₀ ha.ne' h1
    have hlen : euclidNormVec (f (Pi.single μ 1)) = 1 := by
      rw [hf, ← h0, hd, sub_zero, euclidNormVec_single, abs_one]
    have hsum : ∑ ν, (m ν - k ν) ^ 2 = 1 := by
      have h1 : ∑ ν, f (Pi.single μ 1) ν ^ 2 = 1 := by
        unfold TorusMetric.euclidNormVec at hlen
        exact Real.sqrt_eq_one.mp hlen
      simp only [hint] at h1
      exact_mod_cast h1
    obtain ⟨κ, h | h⟩ := int_vec_unit_of_sum_sq_eq_one (fun ν => m ν - k ν) hsum
    · refine ⟨κ, Or.inl (funext fun ν => ?_)⟩
      rw [hint]
      have h1 : m ν - k ν = (Pi.single κ 1 : Fin 4 → ℤ) ν := congrFun h ν
      rw [h1]
      by_cases hν : ν = κ
      · subst hν
        simp
      · simp [Pi.single_eq_of_ne hν]
    · refine ⟨κ, Or.inr (funext fun ν => ?_)⟩
      rw [hint]
      have h1 : m ν - k ν = (-Pi.single κ 1 : Fin 4 → ℤ) ν := congrFun h ν
      rw [h1]
      by_cases hν : ν = κ
      · subst hν
        simp
      · simp [Pi.single_eq_of_ne hν]
  have hmaps : Set.MapsTo f signedUnitVectors signedUnitVectors := by
    rintro x ⟨μ, rfl | rfl⟩
    · exact hbasis μ
    · obtain ⟨κ, h | h⟩ := hbasis μ
      · exact ⟨κ, Or.inr (by rw [map_neg, h])⟩
      · exact ⟨κ, Or.inl (by rw [map_neg, h, neg_neg])⟩
  obtain ⟨w, hw, hwf⟩ := exists_mem_hyperoctahedralLinearGroup f
    ((signedUnitVectors_finite.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj.injOn)
  refine ⟨w, hw, ⟨v₀, hv⟩, fun x => ?_⟩
  have h1 : w x = f x := congrFun hwf x
  rw [h1, hf]
  simp
theorem latticeIsometry_of_affine {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) (v : LatticePoint a)
    {r : AmbientSpace → AmbientSpace} (hr : ∀ x, r x = w x + v) :
    (∀ x y, euclidNormVec (r x - r y) = euclidNormVec (x - y)) ∧
      r '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a := by
  refine ⟨fun x y => ?_, Set.Subset.antisymm ?_ fun y hy => ?_⟩
  · rw [hr, hr, add_sub_add_right_eq_sub, ← map_sub, euclidNormVec_hyperoctahedral hw]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hr]
    exact add_mem (hyperoctahedral_mem_latticeSubgroup hw hx) v.2
  · have hw' : w.symm ∈ hyperoctahedralLinearGroup := inv_mem hw
    refine ⟨w.symm (y - v), hyperoctahedral_mem_latticeSubgroup hw' (sub_mem hy v.2), ?_⟩
    rw [hr]
    simp
theorem affine_parts_unique {w w' : AmbientSpace ≃ₗ[ℝ] AmbientSpace} {v v' : LatticePoint a}
    (h : ∀ x, w x + (v : AmbientSpace) = w' x + (v' : AmbientSpace)) : w = w' ∧ v = v' := by
  have h0 : (v : AmbientSpace) = v' := by simpa using h 0
  refine ⟨LinearEquiv.ext fun x => ?_, Subtype.ext h0⟩
  have hx := h x
  rw [h0] at hx
  exact add_right_cancel hx
theorem mem_motionPerms_iff {g : Equiv.Perm AmbientSpace} :
    g ∈ motionPerms a ↔
      ∃ w ∈ hyperoctahedralLinearGroup, ∃ v : LatticePoint a, ∀ x, g x = w x + v := by
  constructor
  · rintro ⟨w, hw, v, h⟩
    exact ⟨w, hw, v, fun x => congrFun h x⟩
  · rintro ⟨w, hw, v, h⟩
    exact ⟨w, hw, v, funext h⟩
theorem mem_shiftPerms_iff {g : Equiv.Perm AmbientSpace} :
    g ∈ shiftPerms a ↔ ∃ v : LatticePoint a, ∀ x, g x = x + v := by
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v, fun x => congrFun h x⟩
  · rintro ⟨v, h⟩
    exact ⟨v, funext h⟩
theorem mem_hyperoctahedralPerms_iff {g : Equiv.Perm AmbientSpace} :
    g ∈ hyperoctahedralPerms ↔ ∃ w ∈ hyperoctahedralLinearGroup, ∀ x, g x = w x := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, fun x => congrFun h x⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, funext h⟩
def affineSubgroup (a : ℝ) : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := motionPerms a
  mul_mem' := by
    intro g g' hg hg'
    obtain ⟨w, hw, v, h⟩ := mem_motionPerms_iff.mp hg
    obtain ⟨w', hw', v', h'⟩ := mem_motionPerms_iff.mp hg'
    refine mem_motionPerms_iff.mpr
      ⟨w * w', mul_mem hw hw', ⟨w v', hyperoctahedral_mem_latticeSubgroup hw v'.2⟩ + v,
        fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, h', h, map_add, LinearEquiv.mul_apply, AddSubgroup.coe_add,
      add_assoc]
  one_mem' := mem_motionPerms_iff.mpr ⟨1, one_mem _, 0, fun x => by simp⟩
  inv_mem' := by
    intro g hg
    obtain ⟨w, hw, v, h⟩ := mem_motionPerms_iff.mp hg
    have hw' : w.symm ∈ hyperoctahedralLinearGroup := inv_mem hw
    refine mem_motionPerms_iff.mpr
      ⟨w.symm, hw', -⟨w.symm v, hyperoctahedral_mem_latticeSubgroup hw' v.2⟩, fun x => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp
def shiftSubgroup (a : ℝ) : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := shiftPerms a
  mul_mem' := by
    intro g g' hg hg'
    obtain ⟨v, h⟩ := mem_shiftPerms_iff.mp hg
    obtain ⟨v', h'⟩ := mem_shiftPerms_iff.mp hg'
    refine mem_shiftPerms_iff.mpr ⟨v' + v, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, h', h, AddSubgroup.coe_add, add_assoc]
  one_mem' := mem_shiftPerms_iff.mpr ⟨0, fun x => by simp⟩
  inv_mem' := by
    intro g hg
    obtain ⟨v, h⟩ := mem_shiftPerms_iff.mp hg
    refine mem_shiftPerms_iff.mpr ⟨-v, fun x => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp
def pointSubgroup : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := hyperoctahedralPerms
  mul_mem' := by
    intro g g' hg hg'
    obtain ⟨w, hw, h⟩ := mem_hyperoctahedralPerms_iff.mp hg
    obtain ⟨w', hw', h'⟩ := mem_hyperoctahedralPerms_iff.mp hg'
    refine mem_hyperoctahedralPerms_iff.mpr ⟨w * w', mul_mem hw hw', fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, h', h, LinearEquiv.mul_apply]
  one_mem' := mem_hyperoctahedralPerms_iff.mpr ⟨1, one_mem _, fun x => by simp⟩
  inv_mem' := by
    intro g hg
    obtain ⟨w, hw, h⟩ := mem_hyperoctahedralPerms_iff.mp hg
    have hw' : w.symm ∈ hyperoctahedralLinearGroup := inv_mem hw
    refine mem_hyperoctahedralPerms_iff.mpr ⟨w.symm, hw', fun x => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp
theorem shiftSubgroup_le_affine (a : ℝ) : shiftSubgroup a ≤ affineSubgroup a := by
  intro g hg
  obtain ⟨v, h⟩ := mem_shiftPerms_iff.mp hg
  exact mem_motionPerms_iff.mpr ⟨1, one_mem _, v, fun x => by rw [h]; rfl⟩
theorem pointSubgroup_le_affine (a : ℝ) : pointSubgroup ≤ affineSubgroup a := by
  intro g hg
  obtain ⟨w, hw, h⟩ := mem_hyperoctahedralPerms_iff.mp hg
  exact mem_motionPerms_iff.mpr ⟨w, hw, 0, fun x => by rw [h]; simp⟩
theorem shiftSubgroup_normal (a : ℝ) :
    ((shiftSubgroup a).subgroupOf (affineSubgroup a)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u, hu⟩ := mem_shiftPerms_iff.mp hn
  obtain ⟨w, hw, v, h⟩ := mem_motionPerms_iff.mp g.2
  refine mem_shiftPerms_iff.mpr
    ⟨⟨w u, hyperoctahedral_mem_latticeSubgroup hw u.2⟩, fun y => ?_⟩
  have hy : w ((g : Equiv.Perm AmbientSpace)⁻¹ y) + (v : AmbientSpace) = y := by
    rw [← h]
    exact Equiv.apply_symm_apply _ y
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
  rw [h, hu, map_add]
  nth_rewrite 2 [← hy]
  simp only [add_assoc, add_comm (w (u : AmbientSpace)) (v : AmbientSpace)]
theorem shift_point_isComplement (a : ℝ) :
    Subgroup.IsComplement' ((shiftSubgroup a).subgroupOf (affineSubgroup a))
      (pointSubgroup.subgroupOf (affineSubgroup a)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro g hn hh
    rw [Subgroup.mem_subgroupOf] at hn hh
    obtain ⟨v, hv⟩ := mem_shiftPerms_iff.mp hn
    obtain ⟨w, -, hw⟩ := mem_hyperoctahedralPerms_iff.mp hh
    have h0 : (v : AmbientSpace) = 0 := by
      have h1 := hv 0
      rw [hw, map_zero, zero_add] at h1
      exact h1.symm
    refine Subtype.ext (Equiv.ext fun x => ?_)
    rw [hv, h0, add_zero]
    rfl
  · refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨w, hw, v, h⟩ := mem_motionPerms_iff.mp g.2
    have hn : (Equiv.addRight (v : AmbientSpace) : Equiv.Perm AmbientSpace) ∈ shiftSubgroup a :=
      mem_shiftPerms_iff.mpr ⟨v, fun x => rfl⟩
    have hh : (w.toEquiv : Equiv.Perm AmbientSpace) ∈ pointSubgroup :=
      mem_hyperoctahedralPerms_iff.mpr ⟨w, hw, fun x => rfl⟩
    refine Set.mem_mul.mpr
      ⟨⟨_, shiftSubgroup_le_affine a hn⟩, ?_, ⟨_, pointSubgroup_le_affine a hh⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hn
    · exact Subgroup.mem_subgroupOf.mpr hh
    · refine Subtype.ext (Equiv.ext fun x => ?_)
      rw [h]
      rfl
theorem symmetryGroupStatement_holds (h : Tower.OrthogonalMotions.Classification) :
    SymmetryGroupStatement := by
  obtain ⟨-, hI, -⟩ := h
  intro a ha
  refine ⟨fun r => ⟨fun hr => exists_affine_of_latticeIsometry hI ha r hr.1 hr.2, ?_⟩,
    fun w _ w' _ v v' hx => affine_parts_unique hx, ?_,
    ⟨affineSubgroup a, shiftSubgroup a, pointSubgroup, rfl, rfl, rfl, shiftSubgroup_le_affine a,
      pointSubgroup_le_affine a, shiftSubgroup_normal a, shift_point_isComplement a⟩, ?_⟩
  · rintro ⟨w, hw, v, hr⟩
    exact latticeIsometry_of_affine hw v hr
  · rintro f ⟨w, -, v, rfl⟩
    exact ((Equiv.addRight (v : AmbientSpace)).bijective).comp w.bijective
  · intro g hg
    obtain ⟨w, hw, v, hgw⟩ := mem_motionPerms_iff.mp hg
    refine ⟨(v, ⟨w, hw⟩), funext hgw, ?_⟩
    rintro ⟨v', w', hw'⟩ hp
    have hx : ∀ x, (w' : AmbientSpace ≃ₗ[ℝ] AmbientSpace) x + (v' : AmbientSpace) =
        w x + (v : AmbientSpace) := fun x =>
      (congrFun hp x).symm.trans (hgw x)
    obtain ⟨h1, h2⟩ := affine_parts_unique hx
    subst h2
    exact Prod.ext rfl (Subtype.ext h1)
end YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup
end
