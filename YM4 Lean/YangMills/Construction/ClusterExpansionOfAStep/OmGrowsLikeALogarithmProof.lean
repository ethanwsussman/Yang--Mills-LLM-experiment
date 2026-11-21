import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.ClusterExpansionOfAStep.OmGrowsLikeALogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages TorusFields
def quatCoord (g : UnitQuaternion) : Fin 4 → ℝ :=
  ![((g : UnitQuaternion) : ℍ[ℝ]).re, ((g : UnitQuaternion) : ℍ[ℝ]).imI,
    ((g : UnitQuaternion) : ℍ[ℝ]).imJ, ((g : UnitQuaternion) : ℍ[ℝ]).imK]
theorem quatCoord_sum_sq (g : UnitQuaternion) : ∑ i, quatCoord g i ^ 2 = 1 := by
  have hu := (Unitary.mem_iff.mp g.2).1
  rw [Quaternion.star_mul_self] at hu
  have hn : Quaternion.normSq ((g : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    simpa using congrArg (fun z : ℍ[ℝ] => z.re) hu
  rw [Quaternion.normSq_def'] at hn
  simp only [Fin.sum_univ_four, quatCoord]
  simpa using hn
theorem abs_quatCoord_le_one (g : UnitQuaternion) (i : Fin 4) : |quatCoord g i| ≤ 1 := by
  have hsum := quatCoord_sum_sq g
  have hle : quatCoord g i ^ 2 ≤ ∑ j, quatCoord g j ^ 2 :=
    Finset.single_le_sum (f := fun j => quatCoord g j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hsum] at hle
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
theorem re_inv_mul_eq_sum (h g : UnitQuaternion) :
    ((h⁻¹ * g : UnitQuaternion) : ℍ[ℝ]).re = ∑ i, quatCoord h i * quatCoord g i := by
  have hstar : ((h⁻¹ * g : UnitQuaternion) : ℍ[ℝ]) = star (h : ℍ[ℝ]) * (g : ℍ[ℝ]) := by
    rw [Submonoid.coe_mul]
    rfl
  rw [hstar]
  simp [Fin.sum_univ_four, quatCoord, Quaternion.re_mul]
def meshBox (m : ℕ) (g : UnitQuaternion) : Fin 4 → ℤ := fun i => ⌊(m : ℝ) * quatCoord g i⌋
def meshBoxes (m : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) (m : ℤ)
theorem meshBox_mem (m : ℕ) (g : UnitQuaternion) : meshBox m g ∈ meshBoxes m := by
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · apply Int.le_floor.mpr
    have := (abs_le.mp (abs_quatCoord_le_one g i)).1
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  · have hup := (abs_le.mp (abs_quatCoord_le_one g i)).2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : ((⌊(m : ℝ) * quatCoord g i⌋ : ℤ) : ℝ) ≤ (m : ℝ) :=
      (Int.floor_le _).trans (by nlinarith)
    exact_mod_cast this
theorem card_meshBoxes (m : ℕ) : ((meshBoxes m).card : ℝ) = (2 * (m : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
def identityCap (e : ℝ) : Set UnitQuaternion := {g | 1 - e ≤ ((g : UnitQuaternion) : ℍ[ℝ]).re}
theorem continuous_re_unit : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
theorem inv_le_haarUnit_identityCap (m : ℕ) (hm : 1 ≤ m) :
    ((2 * (m : ℝ) + 1) ^ 4)⁻¹ ≤ haarUnit.real (identityCap (2 / (m : ℝ) ^ 2)) := by
  have hcov : (Set.univ : Set UnitQuaternion) ⊆ ⋃ i ∈ meshBoxes m, meshBox m ⁻¹' {i} := by
    intro g _
    exact Set.mem_biUnion (meshBox_mem m g) rfl
  have hsum : (1 : ENNReal) ≤ ∑ i ∈ meshBoxes m, haarUnit (meshBox m ⁻¹' {i}) := by
    calc (1 : ENNReal) = haarUnit Set.univ := by simp
      _ ≤ haarUnit (⋃ i ∈ meshBoxes m, meshBox m ⁻¹' {i}) := measure_mono hcov
      _ ≤ _ := measure_biUnion_finset_le _ _
  have key : ∀ i ∈ meshBoxes m,
      haarUnit (meshBox m ⁻¹' {i}) ≤ haarUnit (identityCap (2 / (m : ℝ) ^ 2)) := by
    intro i _
    by_cases hne : (meshBox m ⁻¹' {i}).Nonempty
    · obtain ⟨h, hh⟩ := hne
      have hsub : meshBox m ⁻¹' {i} ⊆ (fun g => h⁻¹ * g) ⁻¹' identityCap (2 / (m : ℝ) ^ 2) := by
        intro g hg
        have hgh : meshBox m g = meshBox m h := by
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hg hh
          rw [hg, hh]
        have hclose : ∀ j, (quatCoord h j - quatCoord g j) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
          intro j
          have e := congrFun hgh j
          simp only [meshBox] at e
          have a1 := Int.floor_le ((m : ℝ) * quatCoord g j)
          have a2 := Int.lt_floor_add_one ((m : ℝ) * quatCoord g j)
          have b1 := Int.floor_le ((m : ℝ) * quatCoord h j)
          have b2 := Int.lt_floor_add_one ((m : ℝ) * quatCoord h j)
          rw [e] at a1 a2
          have d1 : (m : ℝ) * (quatCoord h j - quatCoord g j) ≤ 1 := by nlinarith
          have d2 : -1 ≤ (m : ℝ) * (quatCoord h j - quatCoord g j) := by nlinarith
          have d3 : ((m : ℝ) * (quatCoord h j - quatCoord g j)) ^ 2 ≤ 1 := sq_le_one_iff_abs_le_one _ |>.mpr (abs_le.mpr ⟨d2, d1⟩)
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        show 1 - 2 / (m : ℝ) ^ 2 ≤ ((h⁻¹ * g : UnitQuaternion) : ℍ[ℝ]).re
        rw [re_inv_mul_eq_sum]
        have hs : ∑ j, (quatCoord h j - quatCoord g j) ^ 2 ≤ 4 * (1 / (m : ℝ) ^ 2) := by
          calc ∑ j, (quatCoord h j - quatCoord g j) ^ 2 ≤ ∑ _j : Fin 4, 1 / (m : ℝ) ^ 2 :=
                Finset.sum_le_sum fun j _ => hclose j
            _ = _ := by simp
        have hexp : ∑ j, (quatCoord h j - quatCoord g j) ^ 2 =
            2 - 2 * ∑ j, quatCoord h j * quatCoord g j := by
          have hh1 := quatCoord_sum_sq h
          have hg1 := quatCoord_sum_sq g
          simp only [Fin.sum_univ_four] at *
          nlinarith
        have : 2 / (m : ℝ) ^ 2 = 2 * (1 / (m : ℝ) ^ 2) := by ring
        rw [this]
        linarith
      calc haarUnit (meshBox m ⁻¹' {i})
            ≤ haarUnit ((fun g => h⁻¹ * g) ⁻¹' identityCap (2 / (m : ℝ) ^ 2)) :=
            measure_mono hsub
        _ = _ := measure_preimage_mul haarUnit h⁻¹ _
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have htot : (1 : ENNReal) ≤
      ((meshBoxes m).card : ENNReal) * haarUnit (identityCap (2 / (m : ℝ) ^ 2)) := by
    calc (1 : ENNReal) ≤ ∑ i ∈ meshBoxes m, haarUnit (meshBox m ⁻¹' {i}) := hsum
      _ ≤ ∑ _i ∈ meshBoxes m, haarUnit (identityCap (2 / (m : ℝ) ^ 2)) := Finset.sum_le_sum key
      _ = _ := by simp
  have hreal : (1 : ℝ) ≤
      ((meshBoxes m).card : ℝ) * haarUnit.real (identityCap (2 / (m : ℝ) ^ 2)) := by
    have := ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)) htot
    simpa [ENNReal.toReal_mul, Measure.real] using this
  rw [card_meshBoxes] at hreal
  have hp : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 4 := by positivity
  rw [inv_le_iff_one_le_mul₀ hp, mul_comm]
  exact hreal
theorem integrable_exp_mul_re (s : ℝ) :
    Integrable (fun g : UnitQuaternion => Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re)) haarUnit :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_re_unit)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
theorem exp_mul_haarUnit_le_partitionFn (s e : ℝ) (hs : 0 ≤ s) (he : IsClosed (identityCap e)) :
    Real.exp (s * (1 - e)) * haarUnit.real (identityCap e) ≤ partitionFn s := by
  have h1 : ∫ g in identityCap e, Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit ≤
      partitionFn s :=
    setIntegral_le_integral (integrable_exp_mul_re s)
      (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)
  have h2 : ∫ _g in identityCap e, Real.exp (s * (1 - e)) ∂haarUnit ≤
      ∫ g in identityCap e, Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit := by
    refine setIntegral_mono_on (integrableOn_const (by simp))
      (integrable_exp_mul_re s).integrableOn he.measurableSet fun g hg => ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hg hs)
  rw [setIntegral_const, smul_eq_mul] at h2
  linarith [mul_comm (haarUnit.real (identityCap e)) (Real.exp (s * (1 - e)))]
theorem isClosed_identityCap (e : ℝ) : IsClosed (identityCap e) :=
  isClosed_le continuous_const continuous_re_unit
theorem logPartitionGap_logGrowth : LogPartitionGapLogGrowth := by
  refine ⟨16, by norm_num, fun s hs => ?_⟩
  set m : ℕ := ⌈Real.sqrt s⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hsq : Real.sqrt s + 0 ≤ m := by
    have : Real.sqrt s ≤ ⌈Real.sqrt s⌉₊ := Nat.le_ceil _
    rw [hm]
    push_cast
    linarith
  have hmu : (m : ℝ) ≤ Real.sqrt s + 2 := by
    have : ((⌈Real.sqrt s⌉₊ : ℕ) : ℝ) < Real.sqrt s + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg s)
    rw [hm]
    push_cast
    linarith
  have hs2 : s ≤ (m : ℝ) ^ 2 := by
    have h1 := Real.sq_sqrt hs
    nlinarith [Real.sqrt_nonneg s]
  have hcap := inv_le_haarUnit_identityCap m hm1
  have hz := exp_mul_haarUnit_le_partitionFn s (2 / (m : ℝ) ^ 2) hs (isClosed_identityCap _)
  have hpos : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 4 := by positivity
  have hlow : Real.exp (s * (1 - 2 / (m : ℝ) ^ 2)) * ((2 * (m : ℝ) + 1) ^ 4)⁻¹ ≤ partitionFn s :=
    (mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le).trans hz
  have hlogz : s * (1 - 2 / (m : ℝ) ^ 2) - 4 * Real.log (2 * (m : ℝ) + 1) ≤
      Real.log (partitionFn s) := by
    have hp : 0 < Real.exp (s * (1 - 2 / (m : ℝ) ^ 2)) * ((2 * (m : ℝ) + 1) ^ 4)⁻¹ := by positivity
    have := Real.log_le_log hp hlow
    rw [Real.log_mul (Real.exp_pos _).ne' (inv_pos.mpr hpos).ne', Real.log_exp, Real.log_inv,
      Real.log_pow] at this
    push_cast at this
    linarith
  have hfrac : s * (2 / (m : ℝ) ^ 2) ≤ 2 := by
    have : s * (2 / (m : ℝ) ^ 2) = 2 * (s / (m : ℝ) ^ 2) := by ring
    rw [this]
    have : s / (m : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hs2
    linarith
  have hL2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogs : Real.log 2 ≤ Real.log (2 + s) := Real.log_le_log (by norm_num) (by linarith)
  have h3 : 2 * (m : ℝ) + 1 ≤ (2 + s) ^ 3 := by
    have h1 := Real.sq_sqrt hs
    have h2 : 2 * Real.sqrt s ≤ 1 + s := by nlinarith [sq_nonneg (Real.sqrt s - 1)]
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs]
  have hlog3 : Real.log (2 * (m : ℝ) + 1) ≤ 3 * Real.log (2 + s) := by
    have := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at this
    exact_mod_cast this
  unfold logPartitionGap
  nlinarith
end YangMills.Construction.TorusLumps
end
