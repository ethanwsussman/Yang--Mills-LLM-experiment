import YangMills.Construction.ReflectionPositivity.UnitNormalReflectionAndLatticeMirrors
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.Mirrors
open YangMills.Construction.InfiniteLattice (AmbientSpace latticeSubgroup)
open YangMills.Construction.PeriodicLattice (coordVec)
namespace UnitNormalAndLattice
theorem dotProduct_self_nonneg_real (v : AmbientSpace) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
theorem normalNorm_pos (H : ReflectingHyperplane) : 0 < H.normalNorm :=
  Real.sqrt_pos.mpr (lt_of_le_of_ne (dotProduct_self_nonneg_real _)
    (dotProduct_self_ne_zero_of_mem H.normalVec_mem).symm)
theorem normalNorm_sq (H : ReflectingHyperplane) : H.normalNorm ^ 2 = H.normalVec ⬝ᵥ H.normalVec :=
  Real.sq_sqrt (dotProduct_self_nonneg_real _)
theorem unitNormalVec_dotProduct (H : ReflectingHyperplane) (x : AmbientSpace) :
    H.unitNormalVec ⬝ᵥ x = (H.normalVec ⬝ᵥ x) / H.normalNorm := by
  rw [ReflectingHyperplane.unitNormalVec, smul_dotProduct, smul_eq_mul, inv_mul_eq_div]
theorem reflect_reflect (H : ReflectingHyperplane) (x : AmbientSpace) :
    H.reflect (H.reflect x) = x :=
  InfiniteLattice.hyperplaneReflect_hyperplaneReflect (dotProduct_self_ne_zero_of_mem H.normalVec_mem) _ x
theorem dotProduct_reflect_sub_offset (H : ReflectingHyperplane) (x : AmbientSpace) :
    H.normalVec ⬝ᵥ H.reflect x - H.offset = -(H.normalVec ⬝ᵥ x - H.offset) :=
  InfiniteLattice.dotProduct_hyperplaneReflect_sub (dotProduct_self_ne_zero_of_mem H.normalVec_mem) _ x
theorem image_latticeSubgroup_eq_iff (H : ReflectingHyperplane) (a : ℝ) (k : Fin 4 → ℤ)
    (hk : ∀ i, H.normalVec i = (k i : ℝ))
    (W : ℤ) (hW : 2 / (H.normalVec ⬝ᵥ H.normalVec) = (W : ℝ)) :
    H.reflect '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a ↔
      ∃ q : ℤ, (W : ℝ) * H.offset = (q : ℝ) * a := by
  have hcoord : ∀ (x : AmbientSpace) (i : Fin 4), H.reflect x i =
      x i - (W : ℝ) * (H.normalVec ⬝ᵥ x - H.offset) * H.normalVec i := by
    intro x i
    rw [← hW]
    simp only [ReflectingHyperplane.reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro h
    have h0 : H.reflect 0 ∈ (latticeSubgroup a : Set AmbientSpace) := by
      rw [← h]
      exact mem_image_of_mem _ (zero_mem (latticeSubgroup a))
    obtain ⟨z, hz⟩ := h0
    obtain ⟨j, hj, -⟩ := exists_first_nonzero_eq_one H.normalVec_mem
    refine ⟨z j, ?_⟩
    have := hz j
    rw [hcoord, hj, dotProduct_zero] at this
    simpa using this
  · rintro ⟨q, hq⟩
    have hmem : ∀ x ∈ (latticeSubgroup a : Set AmbientSpace),
        H.reflect x ∈ (latticeSubgroup a : Set AmbientSpace) := by
      rintro x ⟨p, hp⟩
      have hdot : H.normalVec ⬝ᵥ x = ((∑ j, k j * p j : ℤ) : ℝ) * a := by
        simp only [dotProduct, hk, hp]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      refine ⟨fun i => p i - (W * (∑ j, k j * p j) - q) * k i, fun i => ?_⟩
      rw [hcoord, hdot, hk, hp]
      push_cast
      linear_combination (k i : ℝ) * hq
    apply Subset.antisymm
    · exact image_subset_iff.mpr hmem
    · intro y hy
      exact ⟨H.reflect y, hmem y hy, reflect_reflect H y⟩
theorem coordVec_dotProduct_self (i : Fin 4) :
    coordVec i ⬝ᵥ coordVec i = 1 := by
  simp [coordVec]
theorem diagonal_dotProduct_self (i j : Fin 4) (h : i < j) (v : AmbientSpace)
    (hv : v = coordVec i + coordVec j ∨ v = coordVec i - coordVec j) : v ⬝ᵥ v = 2 := by
  rcases hv with rfl | rfl <;>
    simp [coordVec, dotProduct_add, dotProduct_sub, Pi.single_eq_of_ne h.ne,
      Pi.single_eq_of_ne h.ne'] <;>
    norm_num
theorem diagonal_exists_int_coords (i j : Fin 4) (v : AmbientSpace)
    (hv : v = coordVec i + coordVec j ∨ v = coordVec i - coordVec j) :
    ∃ k : Fin 4 → ℤ, ∀ l, v l = (k l : ℝ) := by
  rcases hv with rfl | rfl
  · refine ⟨Pi.single i 1 + Pi.single j 1, fun l => ?_⟩
    simp only [coordVec, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp <;> norm_num
  · refine ⟨Pi.single i 1 - Pi.single j 1, fun l => ?_⟩
    simp only [coordVec, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp
theorem isometry_reflectL2 (H : ReflectingHyperplane) : Isometry H.reflectL2 := by
  refine Isometry.of_dist_eq fun x y => ?_
  have h := InfiniteLattice.euclidNormVec_hyperplaneReflect_sub
    (dotProduct_self_ne_zero_of_mem H.normalVec_mem) H.offset (WithLp.ofLp x) (WithLp.ofLp y)
  simp only [TorusMetric.euclidNormVec, Pi.sub_apply] at h
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp only [Real.dist_eq, sq_abs]
  exact h
theorem statement_holds : Statement := by
  intro H a ha
  have hN := normalNorm_pos H
  have hN0 : H.normalNorm ≠ 0 := hN.ne'
  have hd0 := dotProduct_self_ne_zero_of_mem H.normalVec_mem
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨dotProduct_reflect_sub_offset H, ?_, isometry_reflectL2 H, ?_⟩, ?_⟩
  · ext x
    simp only [ReflectingHyperplane.carrier, mem_ofPred_eq, unitNormalVec_dotProduct,
      ReflectingHyperplane.signedOffset]
    exact (div_left_inj' hN0).symm
  · intro x
    rw [unitNormalVec_dotProduct, ReflectingHyperplane.unitNormalVec, smul_smul,
      ReflectingHyperplane.reflect, ReflectingHyperplane.signedOffset]
    congr 2
    rw [← normalNorm_sq]
    field_simp
  · ext x
    simp only [ReflectingHyperplane.positiveSide, mem_ofPred_eq, unitNormalVec_dotProduct,
      ReflectingHyperplane.signedOffset, gt_iff_lt]
    exact (div_lt_div_iff_of_pos_right hN).symm
  · intro i hi
    have hone : H.normalVec ⬝ᵥ H.normalVec = 1 := by rw [hi, coordVec_dotProduct_self]
    have hint : ∀ l, H.normalVec l = ((Pi.single i 1 : Fin 4 → ℤ) l : ℝ) := by
      intro l
      rw [hi]
      simp only [coordVec, Pi.single_apply]
      split_ifs <;> simp
    rw [image_latticeSubgroup_eq_iff H a _ hint 2 (by rw [hone]; norm_num)]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      push_cast at hq
      linarith
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      push_cast
      rw [hq]
      ring
  · intro i j hij hv
    obtain ⟨k, hk⟩ := diagonal_exists_int_coords i j H.normalVec hv
    have htwo := diagonal_dotProduct_self i j hij H.normalVec hv
    have hiff := image_latticeSubgroup_eq_iff H a k hk 1 (by rw [htwo]; norm_num)
    have hroot : Real.sqrt 2 * H.signedOffset = H.offset := by
      have h2 : Real.sqrt 2 ≠ 0 := by positivity
      rw [ReflectingHyperplane.signedOffset, ReflectingHyperplane.normalNorm, htwo]
      field_simp
    constructor
    · rw [hiff]
      simp
    · rw [hiff, hroot]
      simp
  · funext x
    exact reflect_reflect H x
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h := dotProduct_reflect_sub_offset H x
      have hx' : H.normalVec ⬝ᵥ x > H.offset := hx
      show H.normalVec ⬝ᵥ H.reflect x < H.offset
      linarith
    · intro hy
      have hy' : H.normalVec ⬝ᵥ y < H.offset := hy
      refine ⟨H.reflect y, ?_, reflect_reflect H y⟩
      have h := dotProduct_reflect_sub_offset H y
      show H.normalVec ⬝ᵥ H.reflect y > H.offset
      linarith
  · intro c x
    have hA : 2 * (H.normalVec ⬝ᵥ x - H.offset) / (H.normalVec ⬝ᵥ H.normalVec) =
        2 * (H.normalVec ⬝ᵥ x - c) / (H.normalVec ⬝ᵥ H.normalVec) -
          2 * (H.offset - c) * (H.normalNorm ^ 2)⁻¹ := by
      rw [normalNorm_sq]
      field_simp
      ring
    change x - (2 * (H.normalVec ⬝ᵥ x - H.offset) / (H.normalVec ⬝ᵥ H.normalVec)) • H.normalVec =
      (x - (2 * (H.normalVec ⬝ᵥ x - c) / (H.normalVec ⬝ᵥ H.normalVec)) • H.normalVec) +
        (2 * (H.offset - c) * (H.normalNorm ^ 2)⁻¹) • H.normalVec
    rw [hA, sub_smul]
    abel
end UnitNormalAndLattice
end YangMills.Construction.Mirrors
