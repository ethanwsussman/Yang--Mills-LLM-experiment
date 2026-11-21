import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometriesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem signedUnitVectors_finite : signedUnitVectors.Finite := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.signedUnitVectors_finite <;> assumption
namespace LatticeSymmetry
variable {a : ℝ} (r : LatticeSymmetry a)
theorem exists_linearEquiv_add_apply_zero :
    ∃ R : AmbientSpace ≃ₗ[ℝ] AmbientSpace, ∀ x, r.toFun x = R x + r.toFun 0 := by
  let e : AmbientSpace ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) := (WithLp.linearEquiv 2 ℝ AmbientSpace).symm
  have hnorm : ∀ x : AmbientSpace, ‖e x‖ = TorusMetric.euclidNormVec x := fun x => by
    simp [e, EuclideanSpace.norm_eq, TorusMetric.euclidNormVec]
  let g : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun y => e (r.toFun (e.symm y))
  have hg : Isometry g := Isometry.of_dist_eq fun y y' => by
    have h := r.preservesDist (e.symm y) (e.symm y')
    rw [dist_eq_norm, dist_eq_norm]
    simp only [g]
    rw [← map_sub, hnorm, h, ← hnorm, map_sub]
    simp
  let A := hg.affineIsometryOfStrictConvexSpace
  let T := A.linearIsometry.toLinearIsometryEquiv rfl
  have hA : ∀ y, g y = T y + g 0 := fun y => by
    have h := A.map_vsub y 0
    simp only [vsub_eq_sub, sub_zero] at h
    have h' : T y = g y - g 0 := h
    rw [h']
    abel
  refine ⟨e.trans (T.toLinearEquiv.trans e.symm), fun x => ?_⟩
  have h := congrArg e.symm (hA (e x))
  simpa [g] using h
theorem toFun_bijective : Function.Bijective r.toFun := by
  obtain ⟨R, hR⟩ := r.exists_linearEquiv_add_apply_zero
  have h : r.toFun = (Equiv.addRight (r.toFun 0)) ∘ R := funext hR
  rw [h]
  exact (Equiv.bijective _).comp R.bijective
def toEquivAmbient : AmbientSpace ≃ AmbientSpace := Equiv.ofBijective r.toFun r.toFun_bijective
theorem toFun_mem_latticeMotions (ha : a ≠ 0) : r.toFun ∈ affineHyperoctahedralMaps a := by
  obtain ⟨R, hR⟩ := r.exists_linearEquiv_add_apply_zero
  have h0 : r.toFun 0 ∈ latticeSubgroup a := (r.pointMap 0).2
  have hdiff : ∀ x, r.toFun x - r.toFun 0 = R x := fun x => by
    rw [hR x]
    abel
  have hpt : ∀ x ∈ latticeSubgroup a, R x ∈ latticeSubgroup a := fun x hx => by
    rw [← hdiff x]
    exact (latticeSubgroup a).sub_mem (r.pointMap ⟨x, hx⟩).2 h0
  have hlen : ∀ x, TorusMetric.euclidNormVec (R x) = TorusMetric.euclidNormVec x := fun x => by
    have h := r.preservesDist x 0
    rwa [hdiff x, sub_zero] at h
  have hstep : ∀ i : Fin 4, (Pi.single i a : AmbientSpace) ∈ latticeSubgroup a :=
    fun i => (axisStep a i).2
  have hmaps : MapsTo R signedUnitVectors signedUnitVectors := by
    intro x hx
    have hax : a • x ∈ latticeSubgroup a := by
      obtain ⟨i, rfl | rfl⟩ := hx
      · have h := hstep i
        rwa [show a • (Pi.single i 1 : AmbientSpace) = Pi.single i a by
          funext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]]
      · have h := (latticeSubgroup a).neg_mem (hstep i)
        rwa [show a • (-Pi.single i 1 : AmbientSpace) = -Pi.single i a by
          funext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [Pi.single_eq_of_ne hj]]
    obtain ⟨n, hn⟩ := hpt _ hax
    have hn' : ∀ i, R x i = n i := fun i => by
      have h := hn i
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm] at h
      exact mul_right_cancel₀ ha h
    have hx1 : TorusMetric.euclidNormVec x = 1 := by
      obtain ⟨i, rfl | rfl⟩ := hx
      · rw [euclidNormVec_single]
        simp
      · rw [← Pi.single_neg, euclidNormVec_single]
        simp
    have hsum : ∑ i, n i ^ 2 = 1 := by
      have h := hlen x
      rw [hx1, TorusMetric.euclidNormVec, Real.sqrt_eq_one] at h
      have h' : ((∑ i, n i ^ 2 : ℤ) : ℝ) = 1 := by
        push_cast
        simpa only [hn'] using h
      exact_mod_cast h'
    obtain ⟨i, h | h⟩ := int_vec_unit_of_sum_sq_eq_one n hsum
    · refine ⟨i, Or.inl ?_⟩
      funext j
      rw [hn', h]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    · refine ⟨i, Or.inr ?_⟩
      funext j
      rw [hn', h]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
  have hbij : BijOn R.toLinearMap signedUnitVectors signedUnitVectors :=
    (signedUnitVectors_finite.injOn_iff_bijOn_of_mapsTo hmaps).1 R.injective.injOn
  obtain ⟨w, hw, hwR⟩ := exists_mem_hyperoctahedralLinearGroup R.toLinearMap hbij
  refine ⟨w, hw, ⟨r.toFun 0, h0⟩, funext fun x => ?_⟩
  rw [hR x, latticeMotion, hwR]
  rfl
end LatticeSymmetry
end YangMills.Construction.InfiniteLattice
