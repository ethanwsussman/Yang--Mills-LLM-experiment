import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.ASegmentInTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GroupPaths
open BlockAverages
theorem norm_unitQuaternion_coe (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unitary_mem_of_norm_eq_one (v : ℍ[ℝ]) (h : ‖v‖ = 1) : v ∈ unitary ℍ[ℝ] := by
  have hs : Quaternion.normSq v = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, h]
    norm_num
  rw [Unitary.mem_iff]
  constructor
  · rw [Quaternion.star_mul_self, hs]
    simp
  · rw [Quaternion.self_mul_star, hs]
    simp
def straightSegment (t : ℝ) (q : UnitQuaternion) : ℍ[ℝ] := 1 + t • ((q : ℍ[ℝ]) - 1)
theorem norm_straightSegment_sq (t : ℝ) (q : UnitQuaternion) :
    ‖straightSegment t q‖ ^ 2 = 1 - t * (1 - t) * ‖(q : ℍ[ℝ]) - 1‖ ^ 2 := by
  set a : ℍ[ℝ] := (q : ℍ[ℝ]) - 1 with ha
  have h1 : ‖(1 : ℍ[ℝ]) + a‖ ^ 2 = 1 := by
    have : (1 : ℍ[ℝ]) + a = q := by rw [ha]; abel
    rw [this, norm_unitQuaternion_coe]
    norm_num
  rw [norm_add_sq_real, norm_one] at h1
  unfold straightSegment
  rw [← ha, norm_add_sq_real, norm_one, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  linear_combination t * h1
theorem straightSegment_norm_bounds (t : ℝ) (q : UnitQuaternion) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hq : ‖(q : ℍ[ℝ]) - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖straightSegment t q‖ ∧ ‖straightSegment t q‖ ≤ 1 ∧
      1 - ‖straightSegment t q‖ ≤ ‖(q : ℍ[ℝ]) - 1‖ ^ 2 := by
  have hs := norm_straightSegment_sq t q
  set n := ‖straightSegment t q‖ with hn
  set a := ‖(q : ℍ[ℝ]) - 1‖ with ha
  have hn0 : 0 ≤ n := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have ht' : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have hp : t * (1 - t) * a ^ 2 ≤ 1 / 4 * a ^ 2 := mul_le_mul_of_nonneg_right ht' (sq_nonneg a)
  have hq0 : 0 ≤ t * (1 - t) * a ^ 2 := by positivity
  have hn1 : n ≤ 1 := by nlinarith
  refine ⟨?_, hn1, ?_⟩
  · nlinarith
  · nlinarith
open Classical in
def normalizedSegment (t : ℝ) (q : UnitQuaternion) : UnitQuaternion :=
  if h : straightSegment t q = 0 then 1 else
    ⟨‖straightSegment t q‖⁻¹ • straightSegment t q, unitary_mem_of_norm_eq_one _ (by
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h))⟩
theorem coe_normalizedSegment (t : ℝ) (q : UnitQuaternion) (h : straightSegment t q ≠ 0) :
    ((normalizedSegment t q : UnitQuaternion) : ℍ[ℝ]) = ‖straightSegment t q‖⁻¹ • straightSegment t q := by
  simp [normalizedSegment, h]
theorem straightSegment_ne_zero (t : ℝ) (q : UnitQuaternion) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hq : ‖(q : ℍ[ℝ]) - 1‖ ≤ 1 / 2) : straightSegment t q ≠ 0 := by
  intro h
  have := (straightSegment_norm_bounds t q ht₀ ht₁ hq).1
  rw [h, norm_zero] at this
  norm_num at this
theorem existsPathFromOne : ExistsPathFromOne := by
  refine ⟨normalizedSegment, ?_, ?_, ?_, ?_⟩
  · intro q
    apply Subtype.ext
    have e : straightSegment 0 q = 1 := by simp [straightSegment]
    rw [coe_normalizedSegment 0 q (by rw [e]; exact one_ne_zero), e]
    simp
  · intro q
    apply Subtype.ext
    have e : straightSegment 1 q = q := by simp [straightSegment]
    have hne : straightSegment 1 q ≠ 0 := by
      rw [e]
      intro h
      have := norm_unitQuaternion_coe q
      rw [h, norm_zero] at this
      norm_num at this
    rw [coe_normalizedSegment 1 q hne, e, norm_unitQuaternion_coe]
    simp
  · intro t q ht₀ ht₁ hq
    obtain ⟨hb1, hb2, hb3⟩ := straightSegment_norm_bounds t q ht₀ ht₁ hq
    have hne := straightSegment_ne_zero t q ht₀ ht₁ hq
    rw [coe_normalizedSegment t q hne]
    change ‖‖straightSegment t q‖⁻¹ • straightSegment t q - straightSegment t q‖ ≤ _
    set n := ‖straightSegment t q‖ with hn
    have hn0 : 0 < n := by linarith
    have e : n⁻¹ • straightSegment t q - straightSegment t q = (n⁻¹ - 1) • straightSegment t q := by
      rw [sub_smul, one_smul]
    rw [e, norm_smul, ← hn, Real.norm_eq_abs]
    have h3 : 0 ≤ n⁻¹ - 1 := by
      have : 1 ≤ n⁻¹ := (one_le_inv₀ hn0).2 hb2
      linarith
    rw [abs_of_nonneg h3, sub_mul, inv_mul_cancel₀ hn0.ne', one_mul]
    exact hb3
  · intro t t' q q' ht₀ ht₁ ht₀' ht₁' hq hq'
    obtain ⟨hb1, hb2, _⟩ := straightSegment_norm_bounds t q ht₀ ht₁ hq
    obtain ⟨hb1', hb2', _⟩ := straightSegment_norm_bounds t' q' ht₀' ht₁' hq'
    rw [coe_normalizedSegment t q (straightSegment_ne_zero t q ht₀ ht₁ hq),
      coe_normalizedSegment t' q' (straightSegment_ne_zero t' q' ht₀' ht₁' hq')]
    set v := straightSegment t q with hv
    set v' := straightSegment t' q' with hv'
    have hn : 0 < ‖v‖ := by linarith
    have hn' : 0 < ‖v'‖ := by linarith
    have hd : ‖v - v'‖ ≤ |t - t'| * ‖(q : ℍ[ℝ]) - 1‖ + ‖(q : ℍ[ℝ]) - (q' : ℍ[ℝ])‖ := by
      have e : v - v' = (t - t') • ((q : ℍ[ℝ]) - 1) + t' • ((q : ℍ[ℝ]) - (q' : ℍ[ℝ])) := by
        rw [hv, hv']
        unfold straightSegment
        simp only [sub_smul, smul_sub]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht₀']
      have : t' * ‖(q : ℍ[ℝ]) - (q' : ℍ[ℝ])‖ ≤ 1 * ‖(q : ℍ[ℝ]) - (q' : ℍ[ℝ])‖ :=
        mul_le_mul_of_nonneg_right ht₁' (norm_nonneg _)
      linarith
    have e2 : ‖v‖⁻¹ • v - ‖v'‖⁻¹ • v' = ‖v‖⁻¹ • (v - v') + (‖v‖⁻¹ - ‖v'‖⁻¹) • v' := by
      rw [smul_sub, sub_smul]
      abel
    rw [e2]
    have h3 : ‖‖v‖⁻¹ • (v - v')‖ ≤ 2 * ‖v - v'‖ := by
      rw [norm_smul, norm_inv, norm_norm]
      have : ‖v‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hn (by norm_num)]
        linarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h4 : ‖(‖v‖⁻¹ - ‖v'‖⁻¹) • v'‖ ≤ 2 * ‖v - v'‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have e3 : (‖v‖⁻¹ - ‖v'‖⁻¹) * ‖v'‖ = (‖v'‖ - ‖v‖) * ‖v‖⁻¹ := by
        field_simp
      have h5 : |‖v‖⁻¹ - ‖v'‖⁻¹| * ‖v'‖ = |‖v'‖ - ‖v‖| * ‖v‖⁻¹ := by
        rw [← abs_of_pos hn', ← abs_mul, abs_of_pos hn', e3, abs_mul, abs_of_pos (inv_pos.2 hn)]
      rw [h5]
      have h6 : |‖v'‖ - ‖v‖| ≤ ‖v - v'‖ := by
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le v v'
      have h7 : ‖v‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hn (by norm_num)]
        linarith
      calc |‖v'‖ - ‖v‖| * ‖v‖⁻¹ ≤ ‖v - v'‖ * 2 :=
            mul_le_mul h6 h7 (by positivity) (norm_nonneg _)
        _ = 2 * ‖v - v'‖ := by ring
    calc _ ≤ ‖‖v‖⁻¹ • (v - v')‖ + ‖(‖v‖⁻¹ - ‖v'‖⁻¹) • v'‖ := norm_add_le _ _
      _ ≤ 4 * ‖v - v'‖ := by linarith
      _ ≤ _ := by linarith
end YangMills.Construction.GroupPaths
end
