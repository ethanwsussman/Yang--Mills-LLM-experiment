import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import YangMills.Construction.InfiniteLattice.TwoMirrorsOfOneFamilyGiveATranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
namespace ReflectionPairShift
theorem euclidNormVec_smul (t : ℝ) (v : AmbientSpace) :
    TorusMetric.euclidNormVec (t • v) = |t| * Real.sqrt (normSq v) := by
  have hq : normSq v = ∑ i, v i ^ 2 := by
    rw [normSq, TorusMetric.euclidNormVec,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hs : ∑ i, (t • v) i ^ 2 = t ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]
  rw [TorusMetric.euclidNormVec, hs, hq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
theorem abs_dotProduct_le_sqrt_normSq_mul (v w : AmbientSpace) :
    |v ⬝ᵥ w| ≤ Real.sqrt (normSq v) * TorusMetric.euclidNormVec w := by
  have hq : normSq v = ∑ i, v i ^ 2 := by
    rw [normSq, TorusMetric.euclidNormVec,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [TorusMetric.euclidNormVec, hq, ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
theorem normSq_pos {v : AmbientSpace} (hv : v ∈ normalSet) : 0 < normSq v := by
  obtain ⟨R, rfl⟩ := exists_reflectionClass hv
  have h := R.realNormal_dot_ne_zero
  rw [← normSq_eq_dotProduct] at h
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm h)
theorem inv_mul_sqrt_eq_inv_sqrt {q : ℝ} (hq : 0 < q) : q⁻¹ * Real.sqrt q = (Real.sqrt q)⁻¹ := by
  calc q⁻¹ * Real.sqrt q = (Real.sqrt q * Real.sqrt q)⁻¹ * Real.sqrt q := by
        rw [Real.mul_self_sqrt hq.le]
    _ = (Real.sqrt q)⁻¹ := by field_simp
theorem planeGap_eq {v : AmbientSpace} (hq : 0 < normSq v) (s s' : ℝ) :
    planeGap v s s' = |s' - s| / Real.sqrt (normSq v) := by
  have hs : 0 < Real.sqrt (normSq v) := Real.sqrt_pos.mpr hq
  have hdot : ∀ t : ℝ, v ⬝ᵥ (t • dualVector v) = t := by
    intro t
    rw [dualVector, smul_smul, dotProduct_smul, ← normSq_eq_dotProduct, smul_eq_mul]
    field_simp
  refine IsLeast.csInf_eq ⟨⟨s • dualVector v, s' • dualVector v, hdot s, hdot s', ?_⟩, ?_⟩
  · have hd : s • dualVector v - s' • dualVector v =
        ((s - s') * (normSq v)⁻¹) • v := by
      rw [dualVector, smul_smul, smul_smul, ← sub_smul, sub_mul]
    rw [hd, euclidNormVec_smul, abs_mul, abs_sub_comm s s', abs_of_pos (inv_pos.mpr hq)]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_sqrt_eq_inv_sqrt hq]
  · rintro g ⟨x, y, hx, hy, rfl⟩
    rw [div_le_iff₀ hs, mul_comm]
    have h := abs_dotProduct_le_sqrt_normSq_mul v (x - y)
    rw [dotProduct_sub, hx, hy, abs_sub_comm] at h
    exact h
theorem isBoundedObservable_reflectObservable (hR : ReflectionIdentities.Statement)
    (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (P.reflectObservable F) := by
  obtain ⟨-, -, -, -, -, -, -, hconj, -⟩ :=
    hR P.normal P.normal_mem P.level P.level P.allowed P.allowed 0
  obtain ⟨hm, C, hC⟩ := hconj F hF
  have heq : P.reflectObservable F = fun U => conj (P.conjReflectObservable F U) := by
    funext U
    simp [NormalLevelPair.conjReflectObservable]
  rw [heq]
  refine ⟨Complex.continuous_conj.measurable.comp hm, C, fun U => ?_⟩
  simpa using hC U
theorem coordVec_normal_facts (i : Fin 4) :
    coordVec i ∈ normalSet ∧ normSq (coordVec i) = 1 ∧
      dualVector (coordVec i) = coordVec i := by
  have hq : normSq (coordVec i) = 1 := by
    rw [normSq_eq_dotProduct]
    simp [coordVec]
  exact ⟨Or.inl ⟨i, rfl⟩, hq, by simp [dualVector, hq]⟩
theorem isAllowedLevel_coordVec_half (i : Fin 4) (k : ℤ) :
    IsAllowedLevel 1 (coordVec i) ((k : ℝ) / 2) := by
  have hq := (coordVec_normal_facts i).2.1
  refine ⟨fun _ => ⟨k, by ring⟩, fun h => ?_⟩
  rw [hq] at h
  norm_num at h
theorem reflectAcross_reflectAcross_coordVec (hR : ReflectionIdentities.Statement) (i : Fin 4)
    (s s' : ℝ) (hs : IsAllowedLevel 1 (coordVec i) s) (hs' : IsAllowedLevel 1 (coordVec i) s')
    (x : AmbientSpace) :
    reflectAcross (coordVec i) s' (reflectAcross (coordVec i) s x) =
      x + (2 * (s' - s)) • coordVec i := by
  obtain ⟨hmem, -, hdual⟩ := coordVec_normal_facts i
  obtain ⟨-, -, h3, -⟩ := hR _ hmem s s' hs hs' 0
  rw [h3 x, hdual]
  rfl
theorem reflectionPairsGiveShift (hR : ReflectionIdentities.Statement) : ReflectionPairsGiveShift := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · intro v hv s s' hs hs'
    have hq := normSq_pos hv
    obtain ⟨-, -, -, -, -, ⟨w, hw, -, hobs⟩, -⟩ := hR v hv s s' hs hs' 0
    have hwv : (w : AmbientSpace) = (2 * (s' - s) * (normSq v)⁻¹) • v := by
      rw [hw, dualVector, smul_smul]
    refine ⟨w, hw, ⟨_, hwv⟩, ?_, planeGap_eq hq s s', ?_⟩
    · rw [planeGap_eq hq, hwv, euclidNormVec_smul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hq)]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv]
      rw [mul_assoc, inv_mul_sqrt_eq_inv_sqrt hq]
      ring
    · intro ρ _ hinv hinv' F hF
      have hthis := hobs F hF
      rw [← hthis]
      exact (hinv' _ (isBoundedObservable_reflectObservable hR _ hF)).trans (hinv F hF)
  · rintro s ⟨k, rfl⟩
    obtain ⟨hmem, hq, -⟩ := coordVec_normal_facts i
    have hs : IsAllowedLevel 1 (coordVec i) ((k : ℝ) + 1 / 2) := by
      have h := isAllowedLevel_coordVec_half i (2 * k + 1)
      have he : (((2 * k + 1 : ℤ) : ℝ)) / 2 = (k : ℝ) + 1 / 2 := by
        push_cast
        ring
      rwa [he] at h
    have hs' : IsAllowedLevel 1 (coordVec i) ((k : ℝ) + 1 / 2 + 1) := by
      have h := isAllowedLevel_coordVec_half i (2 * k + 3)
      have he : (((2 * k + 3 : ℤ) : ℝ)) / 2 = (k : ℝ) + 1 / 2 + 1 := by
        push_cast
        ring
      rwa [he] at h
    refine ⟨⟨_, hmem, _, hs⟩, ⟨_, hmem, _, hs'⟩, rfl, rfl, ⟨hq, k, by ring⟩, rfl, rfl,
      ⟨hq, k + 1, by push_cast; ring⟩, ?_⟩
    funext x
    change reflectAcross _ _ (reflectAcross _ _ x) =
      x + ((axisStep 1 i + axisStep 1 i : LatticePoint 1) : AmbientSpace)
    rw [reflectAcross_reflectAcross_coordVec hR i _ _ hs hs' x]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp [axisStep, coordVec]
      ring
    · simp [axisStep, coordVec, Pi.single_eq_of_ne h]
  · obtain ⟨hmem, hq, -⟩ := coordVec_normal_facts i
    have hs : IsAllowedLevel 1 (coordVec i) 0 := by
      simpa using isAllowedLevel_coordVec_half i 0
    have hs' : IsAllowedLevel 1 (coordVec i) (1 / 2) := by
      simpa using isAllowedLevel_coordVec_half i 1
    refine ⟨⟨_, hmem, _, hs⟩, ⟨_, hmem, _, hs'⟩, rfl, rfl, ⟨hq, 0, by simp⟩, rfl, rfl,
      ⟨hq, 0, by simp⟩, ?_⟩
    funext x
    change reflectAcross _ _ (reflectAcross _ _ x) = x + ((axisStep 1 i : LatticePoint 1) : AmbientSpace)
    rw [reflectAcross_reflectAcross_coordVec hR i _ _ hs hs' x]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp [axisStep, coordVec]
    · simp [axisStep, coordVec, Pi.single_eq_of_ne h]
end ReflectionPairShift
end YangMills.Construction.NormalFamilies
