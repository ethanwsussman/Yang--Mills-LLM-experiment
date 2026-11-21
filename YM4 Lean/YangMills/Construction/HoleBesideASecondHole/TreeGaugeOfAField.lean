import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GaugeFixing
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.LatticeFractionalIntegration
theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
theorem norm_pow_succ_sub_pow_succ_le (a b : ℍ[ℝ]) (e : ℝ) (ha : ‖a‖ ≤ e) (hb : ‖b‖ ≤ e) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * e ^ n * ‖a - b‖ := by
  have he : 0 ≤ e := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
      rw [pow_succ' a, pow_succ' b, mul_sub, sub_mul]
      have : b * b ^ (n + 1) = b ^ (n + 1) * b := (pow_succ' b (n + 1)).symm.trans (pow_succ b (n + 1))
      rw [← pow_succ' b, ← pow_succ' a]
      rw [pow_succ' a (n+1)]
      noncomm_ring
    rw [h1]
    have h2 : ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ ≤ e * ((n + 1) * e ^ n * ‖a - b‖) := by
      rw [norm_mul]
      exact mul_le_mul ha ih (norm_nonneg _) he
    have h3 : ‖(a - b) * b ^ (n + 1)‖ ≤ ‖a - b‖ * e ^ (n + 1) := by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hb _
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ e * ((n + 1) * e ^ n * ‖a - b‖) + ‖a - b‖ * e ^ (n + 1) := add_le_add h2 h3
      _ = _ := by push_cast; ring
theorem norm_exp_sub_exp_sub_sub_le (a b : ℍ[ℝ]) (ha : ‖a‖ ≤ 1 / 4) (hb : ‖b‖ ≤ 1 / 4) :
    ‖NormedSpace.exp a - NormedSpace.exp b - (a - b)‖ ≤ (1 / 2) * ‖a - b‖ := by
  have Ha := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a
  have Hb := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) b
  have Hd := Ha.sub Hb
  have H2 := (hasSum_nat_add_iff' 2).2 Hd
  have hsum : ∑ i ∈ Finset.range 2, (((i.factorial : ℝ)⁻¹ • a ^ i) - ((i.factorial : ℝ)⁻¹ • b ^ i)) = a - b := by
    simp [Finset.sum_range_succ]
  rw [hsum] at H2
  have hg : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * ‖a - b‖) ((1 / 3 : ℝ) * ‖a - b‖) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_right ((1 / 4 : ℝ) * ‖a - b‖)
    have e1 : (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * ‖a - b‖) =
        fun i : ℕ => (1 / 4 : ℝ) ^ i * ((1 / 4 : ℝ) * ‖a - b‖) := by funext n; ring
    have e2 : (1 / 3 : ℝ) * ‖a - b‖ = (1 - 1 / 4 : ℝ)⁻¹ * ((1 / 4 : ℝ) * ‖a - b‖) := by norm_num; ring
    rw [e1, e2]
    exact this
  have hle := H2.norm_le_of_bounded hg (by
    intro n
    have h1 := norm_pow_succ_sub_pow_succ_le a b (1 / 4) ha hb (n + 1)
    rw [← smul_sub, norm_smul]
    have hf : ((n + 1 + 1 : ℕ) : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      have : (n + 1 + 1) ≤ (n + 2).factorial := Nat.self_le_factorial _
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((n + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [Real.norm_of_nonneg (by positivity)]
    have h2 : ‖a ^ (n + 2) - b ^ (n + 2)‖ ≤ ((n + 2).factorial : ℝ) * ((1 / 4 : ℝ) ^ (n + 1) * ‖a - b‖) := by
      refine h1.trans ?_
      have : (((n + 1 : ℕ) : ℝ) + 1) ≤ ((n + 2).factorial : ℝ) := by
        push_cast at hf ⊢; linarith
      have hnn : 0 ≤ (1 / 4 : ℝ) ^ (n + 1) * ‖a - b‖ := by positivity
      nlinarith
    rw [inv_mul_le_iff₀ hpos]
    exact h2)
  exact hle.trans (by nlinarith [norm_nonneg (a - b)])
theorem norm_exp_sub_exp_le (a b : ℍ[ℝ]) (ha : ‖a‖ ≤ 1 / 4) (hb : ‖b‖ ≤ 1 / 4) :
    ‖NormedSpace.exp a - NormedSpace.exp b‖ ≤ 2 * ‖a - b‖ := by
  have h := norm_exp_sub_exp_sub_sub_le a b ha hb
  have h2 : ‖NormedSpace.exp a - NormedSpace.exp b‖ ≤
      ‖NormedSpace.exp a - NormedSpace.exp b - (a - b)‖ + ‖a - b‖ := by
    simpa using norm_add_le (NormedSpace.exp a - NormedSpace.exp b - (a - b)) (a - b)
  nlinarith [norm_nonneg (a - b)]
theorem norm_sub_le_two_mul_norm_exp_sub_exp (a b : ℍ[ℝ]) (ha : ‖a‖ ≤ 1 / 4) (hb : ‖b‖ ≤ 1 / 4) :
    ‖a - b‖ ≤ 2 * ‖NormedSpace.exp a - NormedSpace.exp b‖ := by
  have h := norm_exp_sub_exp_sub_sub_le a b ha hb
  have h2 : ‖a - b‖ ≤ ‖NormedSpace.exp a - NormedSpace.exp b‖ +
      ‖NormedSpace.exp a - NormedSpace.exp b - (a - b)‖ := by
    have := norm_sub_le (NormedSpace.exp a - NormedSpace.exp b) (NormedSpace.exp a - NormedSpace.exp b - (a - b))
    simpa using this
  nlinarith [norm_nonneg (a - b)]
theorem coe_expUnit_eq (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = ((Real.cos ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) +
      (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) :=
  Quaternion.exp_of_re_eq_zero _ w.2
theorem re_coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]).re = Real.cos ‖(w : ℍ[ℝ])‖ := by
  rw [coe_expUnit_eq]
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  simp [hw]
theorem normSq_coe_unitQuaternion (g : UnitQuaternion) : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.normSq_unitQuaternion <;> assumption
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem re_sq_add_norm_im_sq (q : ℍ[ℝ]) : q.re ^ 2 + ‖q.im‖ ^ 2 = ‖q‖ ^ 2 := by
  have h1 := Quaternion.normSq_eq_norm_mul_self q
  have h2 := Quaternion.normSq_eq_norm_mul_self q.im
  rw [Quaternion.normSq_def'] at h1 h2
  simp only [Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im] at h2
  nlinarith
def imagUnitI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
theorem exists_log_cos_norm_eq_re (g : UnitQuaternion) :
    ∃ w : imaginaryQuaternions, expUnit w = g ∧ Real.cos ‖(w : ℍ[ℝ])‖ = (g : ℍ[ℝ]).re ∧
      ‖(w : ℍ[ℝ])‖ ≤ Real.pi := by
  set q : ℍ[ℝ] := (g : ℍ[ℝ]) with hq
  have hnorm : q.re ^ 2 + ‖q.im‖ ^ 2 = 1 := by
    rw [re_sq_add_norm_im_sq, hq, norm_coe_unitQuaternion]; norm_num
  have hre1 : q.re ≤ 1 := by nlinarith [sq_nonneg ‖q.im‖, sq_nonneg (q.re - 1)]
  have hre2 : -1 ≤ q.re := by nlinarith [sq_nonneg ‖q.im‖, sq_nonneg (q.re + 1)]
  by_cases hv : q.im = 0
  · have hsq : (q.re - 1) * (q.re + 1) = 0 := by rw [hv, norm_zero] at hnorm; nlinarith
    have hq' : q = ((q.re : ℝ) : ℍ[ℝ]) := by
      have := Quaternion.re_add_im q
      rw [hv] at this
      simpa using this.symm
    rcases mul_eq_zero.1 hsq with h | h
    · have h1 : q.re = 1 := by linarith
      refine ⟨0, ?_, ?_, ?_⟩
      · apply Subtype.ext
        show NormedSpace.exp ((0 : imaginaryQuaternions) : ℍ[ℝ]) = q
        rw [hq', h1]; simp
      · simp [h1]
      · simpa using Real.pi_pos.le
    · have h1 : q.re = -1 := by linarith
      have hI : imagUnitI.re = 0 := rfl
      have hmem : (Real.pi • imagUnitI).re = 0 := by simp [hI]
      have hn1 : ‖imagUnitI‖ = 1 := by
        have hs : Quaternion.normSq imagUnitI = 1 := by
          rw [Quaternion.normSq_def']
          show (0 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
          norm_num
        have h5 := Quaternion.normSq_eq_norm_mul_self imagUnitI
        rw [hs] at h5
        rcases mul_self_eq_one_iff.1 h5.symm with h6 | h6
        · exact h6
        · have := norm_nonneg imagUnitI
          linarith
      have hn : ‖Real.pi • imagUnitI‖ = Real.pi := by
        rw [norm_smul, hn1, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
      refine ⟨⟨_, hmem⟩, ?_, ?_, ?_⟩
      · apply Subtype.ext
        show NormedSpace.exp (Real.pi • imagUnitI) = q
        rw [Quaternion.exp_of_re_eq_zero _ hmem, hn, hq', h1]
        simp
      · show Real.cos ‖Real.pi • imagUnitI‖ = q.re
        rw [hn, h1]; simp
      · show ‖Real.pi • imagUnitI‖ ≤ Real.pi
        rw [hn]
  · have hvpos : 0 < ‖q.im‖ := norm_pos_iff.2 hv
    set θ := Real.arccos q.re with hθ
    have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
    have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
    have hcos : Real.cos θ = q.re := Real.cos_arccos hre2 hre1
    have hsin : Real.sin θ = ‖q.im‖ := by
      rw [hθ, Real.sin_arccos]
      have : 1 - q.re ^ 2 = ‖q.im‖ ^ 2 := by linarith
      rw [this, Real.sqrt_sq (norm_nonneg _)]
    have hθne : θ ≠ 0 := by
      intro h0
      rw [h0] at hsin
      simp at hsin
      exact hv (norm_eq_zero.1 hsin.symm)
    have hmem : ((θ / ‖q.im‖) • q.im).re = 0 := by simp
    have hn : ‖(θ / ‖q.im‖) • q.im‖ = θ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    refine ⟨⟨_, hmem⟩, ?_, ?_, ?_⟩
    · apply Subtype.ext
      show NormedSpace.exp ((θ / ‖q.im‖) • q.im) = q
      rw [Quaternion.exp_of_re_eq_zero _ hmem, hn, hcos, hsin, smul_smul]
      have : ‖q.im‖ / θ * (θ / ‖q.im‖) = 1 := by field_simp
      rw [this, one_smul]
      exact Quaternion.re_add_im q
    · show Real.cos ‖(θ / ‖q.im‖) • q.im‖ = q.re
      rw [hn, hcos]
    · show ‖(θ / ‖q.im‖) • q.im‖ ≤ Real.pi
      rw [hn]; exact hθpi
theorem minimalLog_spec (g : UnitQuaternion) :
    expUnit (minimalLog g) = g ∧
      ∀ w' : imaginaryQuaternions, expUnit w' = g → ‖(minimalLog g : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖ := by
  obtain ⟨w, hw, hc, hpi⟩ := exists_log_cos_norm_eq_re g
  have h : ∃ w : imaginaryQuaternions, expUnit w = g ∧
      ∀ w' : imaginaryQuaternions, expUnit w' = g → ‖(w : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖ := by
    refine ⟨w, hw, fun w' hw' => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 : Real.cos ‖(w' : ℍ[ℝ])‖ = (g : ℍ[ℝ]).re := by rw [← re_coe_expUnit, hw']
    have h2 := Real.strictAntiOn_cos ⟨norm_nonneg _, hlt.le.trans hpi⟩ ⟨norm_nonneg _, hpi⟩ hlt
    rw [hc, h1] at h2
    exact lt_irrefl _ h2
  have : minimalLog g = h.choose := dif_pos h
  rw [this]
  exact h.choose_spec
theorem expUnit_minimalLog (g : UnitQuaternion) : expUnit (minimalLog g) = g := (minimalLog_spec g).1
theorem norm_minimalLog_le_pi (g : UnitQuaternion) : ‖(minimalLog g : ℍ[ℝ])‖ ≤ Real.pi := by
  obtain ⟨w, hw, -, hpi⟩ := exists_log_cos_norm_eq_re g
  exact ((minimalLog_spec g).2 w hw).trans hpi
theorem norm_coe_sub_one_sq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by
  have h1 := normSq_coe_unitQuaternion g
  have h2 := Quaternion.normSq_eq_norm_mul_self ((g : ℍ[ℝ]) - 1)
  rw [Quaternion.normSq_def'] at h1 h2
  simp at h2
  nlinarith
theorem norm_minimalLog_le (g : UnitQuaternion) : ‖(minimalLog g : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by
  set θ := ‖(minimalLog g : ℍ[ℝ])‖ with hθ
  have hpi : θ ≤ Real.pi := norm_minimalLog_le_pi g
  have h0 : 0 ≤ θ := norm_nonneg _
  have hre : (g : ℍ[ℝ]).re = Real.cos θ := by
    have := re_coe_expUnit (minimalLog g)
    rw [expUnit_minimalLog] at this
    exact this
  have hs : 2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hs2 : θ / 4 ≤ Real.sin (θ / 2) := by
    refine le_trans ?_ hs
    have : 2 / Real.pi * (θ / 2) = θ / Real.pi := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left h0 Real.pi_pos hpi4
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h3 := Real.cos_two_mul (θ / 2)
    have h4 := Real.sin_sq_add_cos_sq (θ / 2)
    have : 2 * (θ / 2) = θ := by ring
    rw [this] at h3
    nlinarith
  have hsq := norm_coe_sub_one_sq g
  rw [hre, hc] at hsq
  have h5 : (θ / 2) ^ 2 ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ θ / 4) hs2]
  have h6 := abs_le_of_sq_le_sq' h5 (norm_nonneg _)
  linarith [h6.2]
theorem minimalLog_expUnit (w : imaginaryQuaternions) (hw : ‖(w : ℍ[ℝ])‖ < Real.pi) :
    minimalLog (expUnit w) = w := by
  obtain ⟨h1, h2⟩ := minimalLog_spec (expUnit w)
  set l := minimalLog (expUnit w) with hl
  have hle := h2 w rfl
  have hc : Real.cos ‖(l : ℍ[ℝ])‖ = Real.cos ‖(w : ℍ[ℝ])‖ := by
    rw [← re_coe_expUnit, ← re_coe_expUnit, h1]
  have heq : ‖(l : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ :=
    Real.injOn_cos ⟨norm_nonneg _, hle.trans hw.le⟩ ⟨norm_nonneg _, hw.le⟩ hc
  by_cases h0 : ‖(w : ℍ[ℝ])‖ = 0
  · apply Subtype.ext
    rw [norm_eq_zero.1 h0, norm_eq_zero.1 (heq.trans h0)]
  have hpos : 0 < ‖(w : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hsin : 0 < Real.sin ‖(w : ℍ[ℝ])‖ := Real.sin_pos_of_pos_of_lt_pi hpos hw
  have h3 := congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) h1
  simp only [coe_expUnit_eq, heq] at h3
  have h4 := add_left_cancel h3
  have hne : Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖ ≠ 0 := (div_pos hsin hpos).ne'
  exact Subtype.ext (smul_right_injective _ hne h4)
theorem norm_coe_expUnit_sub_one_le (w : imaginaryQuaternions) (hw : ‖(w : ℍ[ℝ])‖ ≤ 1 / 4) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ‖(w : ℍ[ℝ])‖ := by
  have := norm_exp_sub_exp_le (w : ℍ[ℝ]) 0 hw (by simp)
  simpa [coe_expUnit] using this
theorem norm_minimalLog_sub_minimalLog_le (g g' : UnitQuaternion) (hg : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 8)
    (hg' : ‖(g' : ℍ[ℝ]) - 1‖ ≤ 1 / 8) :
    ‖(minimalLog g : ℍ[ℝ]) - minimalLog g'‖ ≤ 2 * ‖(g : ℍ[ℝ]) - g'‖ := by
  have h1 := (norm_minimalLog_le g).trans (by linarith : 2 * ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 4)
  have h2 := (norm_minimalLog_le g').trans (by linarith : 2 * ‖(g' : ℍ[ℝ]) - 1‖ ≤ 1 / 4)
  have := norm_sub_le_two_mul_norm_exp_sub_exp _ _ h1 h2
  rw [← coe_expUnit, ← coe_expUnit, expUnit_minimalLog, expUnit_minimalLog] at this
  exact this
section Cells
variable {F : BlockFrame}
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_depth (F : BlockFrame) (i : Fin 4) :
    ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) := by
  simp [BlockFrame.period]
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by
  simp [BlockFrame.period]
def halfSide (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem blockSide_eq_two_mul_halfSide_add_one (hL : Odd F.blockSide) :
    (F.blockSide : ℤ) = 2 * halfSide F.blockSide + 1 := by
  obtain ⟨k, hk⟩ := hL
  simp only [halfSide, hk]
  push_cast
  omega
theorem mem_centredCube {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ i, -halfSide M ≤ o i ∧ o i ≤ halfSide M := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem mem_centredCube_iff_abs_le {M : ℕ} {o : Fin 4 → ℤ} : o ∈ centredCube M ↔ ∀ i, |o i| ≤ halfSide M := by
  rw [mem_centredCube]
  exact forall_congr' fun i => abs_le.symm
theorem enclosingCell_cellCentre_add (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (y : F.Cell)
    (o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth y + siteOfCoords F.depth o) = y := by
  funext i
  have hnt := top_sub_depth F
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hoi := mem_centredCube.1 ho i
  set u : ℤ := (F.blockSide : ℤ) * siteCoords y i + o i with hu
  have hx : (cellCentre F.depth y + siteOfCoords F.depth o : F.Site F.depth) i =
      ((u : ℤ) : ZMod (F.period F.depth i)) := by
    simp [cellCentre, siteOfCoords, hnt, hu]
  have hc : siteCoords (cellCentre F.depth y + siteOfCoords F.depth o : F.Site F.depth) i =
      u % ((F.period F.depth i : ℕ) : ℤ) := by
    show ZMod.cast ((cellCentre F.depth y + siteOfCoords F.depth o : F.Site F.depth) i) = _
    rw [hx]
    exact ZMod.coe_intCast u
  have hper := period_depth F i
  set m : ℤ := (F.extent i : ℤ) with hm
  set k : ℤ := u / ((F.period F.depth i : ℕ) : ℤ) with hk
  have hLne : (F.blockSide : ℤ) ≠ 0 := by omega
  have key : (u % ((F.period F.depth i : ℕ) : ℤ) + halfSide F.blockSide) / (F.blockSide : ℤ) =
      siteCoords y i - m * k := by
    have h1 : u % ((F.period F.depth i : ℕ) : ℤ) + halfSide F.blockSide =
        (o i + halfSide F.blockSide) + (F.blockSide : ℤ) * (siteCoords y i - m * k) := by
      rw [Int.emod_def, ← hk, hper, hu]
      ring
    rw [h1, Int.add_mul_ediv_left _ _ hLne, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    ring
  have hy : y i = ((siteCoords y i : ℤ) : ZMod (F.period F.top i)) := by simp [siteCoords]
  simp only [enclosingCell, siteOfCoords, hnt, pow_one]
  show (((siteCoords (cellCentre F.depth y + siteOfCoords F.depth o : F.Site F.depth) i +
      ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) : ℤ) : ZMod (F.period F.top i)) = y i
  rw [hc]
  change (((u % ((F.period F.depth i : ℕ) : ℤ) + halfSide F.blockSide) / (F.blockSide : ℤ) : ℤ) :
    ZMod (F.period F.top i)) = y i
  rw [key, hy, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨k, ?_⟩
  rw [period_top]
  ring
theorem cellOffset_cellCentre_add (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (y : F.Cell)
    (o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth y + siteOfCoords F.depth o) = o := by
  funext i
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hoi := mem_centredCube_iff_abs_le.1 ho i
  have hper := period_depth F i
  have hsi : (1 : ℤ) ≤ (F.extent i : ℤ) := by exact_mod_cast hs i
  have hbig : 2 * |o i| < ((F.period F.depth i : ℕ) : ℤ) := by
    rw [hper]
    nlinarith
  simp only [cellOffset, enclosingCell_cellCentre_add hs hL y o ho, add_sub_cancel_left]
  exact valMinAbs_intCast_of_small (Or.inr hbig)
theorem exists_eq_cellCentre_add (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (x : F.Site F.depth) :
    ∃ (y : F.Cell) (o : Fin 4 → ℤ), o ∈ centredCube F.blockSide ∧
      x = cellCentre F.depth y + siteOfCoords F.depth o := by
  have hnt := top_sub_depth F
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by
    have : 0 < F.blockSide := hL.pos
    exact_mod_cast this
  set q : Fin 4 → ℤ := fun i => (siteCoords x i + halfSide F.blockSide) / (F.blockSide : ℤ) with hq
  set r : Fin 4 → ℤ := fun i =>
    (siteCoords x i + halfSide F.blockSide) % (F.blockSide : ℤ) - halfSide F.blockSide with hr
  refine ⟨siteOfCoords F.top q, r, ?_, ?_⟩
  · rw [mem_centredCube]
    intro i
    have h1 := Int.emod_nonneg (siteCoords x i + halfSide F.blockSide) hLpos.ne'
    have h2 := Int.emod_lt_of_pos (siteCoords x i + halfSide F.blockSide) hLpos
    simp only [hr]
    omega
  · funext i
    have hxi : x i = ((siteCoords x i : ℤ) : ZMod (F.period F.depth i)) := by simp [siteCoords]
    have hcy : siteCoords (siteOfCoords (F := F) F.top q) i = q i % ((F.period F.top i : ℕ) : ℤ) := by
      show ZMod.cast (((q i : ℤ) : ZMod (F.period F.top i))) = _
      exact ZMod.coe_intCast _
    have hsum : (cellCentre F.depth (siteOfCoords (F := F) F.top q) + siteOfCoords F.depth r :
        F.Site F.depth) i =
        (((F.blockSide : ℤ) * (q i % ((F.period F.top i : ℕ) : ℤ)) + r i : ℤ) :
          ZMod (F.period F.depth i)) := by
      simp [cellCentre, siteOfCoords, hnt, hcy]
    rw [hsum, hxi, ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨q i / ((F.period F.top i : ℕ) : ℤ) * (-1), ?_⟩
    have hd := Int.emod_add_mul_ediv (siteCoords x i + halfSide F.blockSide) (F.blockSide : ℤ)
    have hd2 := Int.emod_add_mul_ediv (q i) ((F.period F.top i : ℕ) : ℤ)
    rw [period_depth, ← period_top F i]
    simp only [hr]
    simp only [hq] at hd2 ⊢
    have e1 : (F.blockSide : ℤ) * ((siteCoords x i + halfSide F.blockSide) / (F.blockSide : ℤ) %
        ((F.period F.top i : ℕ) : ℤ)) =
        (F.blockSide : ℤ) * ((siteCoords x i + halfSide F.blockSide) / (F.blockSide : ℤ)) -
          (F.blockSide : ℤ) * (((F.period F.top i : ℕ) : ℤ) *
          ((siteCoords x i + halfSide F.blockSide) / (F.blockSide : ℤ) / ((F.period F.top i : ℕ) : ℤ))) := by
      rw [← mul_sub]
      congr 1
      linarith
    rw [e1]
    linarith
theorem cellOffset_mem_and_eq (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (x : F.Site F.depth) :
    cellOffset x ∈ centredCube F.blockSide ∧
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by
  obtain ⟨y, o, ho, rfl⟩ := exists_eq_cellCentre_add hs hL x
  rw [cellOffset_cellCentre_add hs hL y o ho, enclosingCell_cellCentre_add hs hL y o ho]
  exact ⟨ho, rfl⟩
theorem sitesBelow_depth (y : F.Cell) :
    sitesBelow F.depth y =
      (centredCube F.blockSide).image fun h => cellCentre F.depth y + siteOfCoords F.depth h := by
  have hnt := top_sub_depth F
  simp only [sitesBelow, hnt, pow_one]
  apply Finset.image_congr
  intro h _
  funext i
  simp [cellCentre, siteOfCoords, hnt]
theorem mem_sitesBelow_depth (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (y : F.Cell)
    (x : F.Site F.depth) : x ∈ sitesBelow F.depth y ↔ enclosingCell x = y := by
  rw [sitesBelow_depth]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact enclosingCell_cellCentre_add hs hL y o ho
  · rintro rfl
    exact ⟨_, (cellOffset_mem_and_eq hs hL x).1, (cellOffset_mem_and_eq hs hL x).2⟩
theorem mem_cutBelow_depth (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (x : F.Site F.depth) : x ∈ cutBelow F.depth S ↔ enclosingCell x ∈ S := by
  simp only [cutBelow, Finset.mem_biUnion, mem_sitesBelow_depth hs hL]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨_, h, rfl⟩
end Cells
section Paths
variable {F : BlockFrame}
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by
  induction l with
  | nil => intro x; simp [pathHolonomy, pathDisplacement]
  | cons st r ih =>
    intro x
    simp only [List.cons_append, pathHolonomy]
    rw [ih, mul_assoc]
    have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [this]
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by
  simp [pathDisplacement]
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by
  induction l with
  | nil => simp [pathDisplacement, reversePath]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [e, pathDisplacement_append, ih]
    obtain ⟨i, b⟩ := st
    cases b <;> simp [pathDisplacement, stepDisplacement, add_comm]
theorem linkValue_reverse {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by
  obtain ⟨i, b⟩ := st
  cases b
  · simp [linkValue, stepDisplacement, sub_eq_add_neg]
  · simp [linkValue, stepDisplacement]
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by
  induction l with
  | nil => intro x; simp [pathHolonomy, pathDisplacement, reversePath]
  | cons st r ih =>
    intro x
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e2 : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    rw [e, pathHolonomy_append, e2, ih, pathDisplacement_reversePath]
    simp only [pathHolonomy, add_neg_cancel_right, mul_one, mul_inv_rev]
    rw [linkValue_reverse]
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (x : F.Site j) (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by
  obtain ⟨i, b⟩ := st
  cases b
  · simp [linkValue, stepDisplacement, gaugeTransform, sub_eq_add_neg, mul_assoc]
  · simp [linkValue, stepDisplacement, gaugeTransform]
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by
  induction l with
  | nil => intro x; simp [pathHolonomy, pathDisplacement]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    rw [ih, linkValue_gaugeTransform]
    have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [this]
    group
def PathWithin {j : ℕ} (Q : Finset (F.Site j)) : F.Site j → List PathStep → Prop
  | x, [] => x ∈ Q
  | x, st :: r => x ∈ Q ∧ PathWithin Q (x + stepDisplacement j st) r
theorem PathWithin.head_mem {j : ℕ} {Q : Finset (F.Site j)} {x : F.Site j} {l : List PathStep}
    (h : PathWithin Q x l) : x ∈ Q := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem linkValue_congr {j : ℕ} {Q : Finset (F.Site j)} {X X' : F.GaugeField j}
    (h : ∀ b ∈ cutBonds Q, X b.1 b.2 = X' b.1 b.2) {x : F.Site j} {st : PathStep} (hx : x ∈ Q)
    (hx' : x + stepDisplacement j st ∈ Q) : linkValue X x st = linkValue X' x st := by
  obtain ⟨i, b⟩ := st
  cases b
  · have hm : (x - unitStep j i, i) ∈ cutBonds Q := by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · simpa [stepDisplacement, sub_eq_add_neg] using hx'
      · simpa using hx
    simp [linkValue, h _ hm]
  · have hm : (x, i) ∈ cutBonds Q := by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨hx, by simpa [stepDisplacement] using hx'⟩
    simp [linkValue, h _ hm]
theorem pathHolonomy_congr {j : ℕ} {Q : Finset (F.Site j)} {X X' : F.GaugeField j}
    (h : ∀ b ∈ cutBonds Q, X b.1 b.2 = X' b.1 b.2) (l : List PathStep) :
    ∀ x, PathWithin Q x l → pathHolonomy X x l = pathHolonomy X' x l := by
  induction l with
  | nil => intro x _; rfl
  | cons st r ih =>
    intro x hp
    simp only [pathHolonomy]
    rw [linkValue_congr h hp.1 hp.2.head_mem, ih _ hp.2]
theorem pathWithin_mono {j : ℕ} {Q Q' : Finset (F.Site j)} (hQ : Q ⊆ Q') (l : List PathStep) :
    ∀ x, PathWithin Q x l → PathWithin Q' x l := by
  induction l with
  | nil => intro x h; exact hQ h
  | cons st r ih => intro x h; exact ⟨hQ h.1, ih _ h.2⟩
theorem pathWithin_append {j : ℕ} {Q : Finset (F.Site j)} (l l' : List PathStep) :
    ∀ x, PathWithin Q x l → PathWithin Q (x + pathDisplacement j l) l' → PathWithin Q x (l ++ l') := by
  induction l with
  | nil => intro x _ h; simpa [pathDisplacement] using h
  | cons st r ih =>
    intro x h h'
    refine ⟨h.1, ih _ h.2 ?_⟩
    have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rwa [this]
theorem pathWithin_reversePath {j : ℕ} {Q : Finset (F.Site j)} (l : List PathStep) :
    ∀ x, PathWithin Q x l → PathWithin Q (x + pathDisplacement j l) (reversePath l) := by
  induction l with
  | nil =>
    intro x h
    simp only [pathDisplacement, List.map_nil, List.sum_nil, add_zero]
    exact h
  | cons st r ih =>
    intro x h
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e2 : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    rw [e, e2]
    refine pathWithin_append _ _ _ (ih _ h.2) ?_
    rw [pathDisplacement_reversePath, add_neg_cancel_right]
    refine ⟨h.2.head_mem, ?_⟩
    have : x + stepDisplacement j st + stepDisplacement j (st.1, !st.2) = x := by
      obtain ⟨i, b⟩ := st
      cases b <;> simp [stepDisplacement]
    show x + stepDisplacement j st + stepDisplacement j (st.1, !st.2) ∈ Q
    rw [this]
    exact h.1
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by
  simp [pathDisplacement, List.map_replicate, List.sum_replicate]
theorem pathWithin_replicate {j : ℕ} {Q : Finset (F.Site j)} (st : PathStep) (n : ℕ) :
    ∀ x, (∀ k ≤ n, x + k • stepDisplacement j st ∈ Q) → PathWithin Q x (List.replicate n st) := by
  induction n with
  | zero => intro x h; simpa [PathWithin] using h 0 le_rfl
  | succ n ih =>
    intro x h
    refine ⟨by simpa using h 0 (Nat.zero_le _), ih _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    have e : x + stepDisplacement j st + k • stepDisplacement j st = x + (k + 1) • stepDisplacement j st := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [e]
    exact this
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
theorem siteOfCoords_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by
  funext k
  simp [siteOfCoords, unitStep]
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_zero <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by
  funext k
  simp only [siteOfCoords, unitStep, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb.symm]
  · simp
theorem pathDisplacement_replicate_axis (j : ℕ) (c : ℤ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate c.natAbs (i, decide (0 ≤ c))) = c • unitStep j i := by
  rw [pathDisplacement_replicate]
  by_cases hc : 0 ≤ c
  · simp only [stepDisplacement, hc, decide_true, if_true]
    rw [← natCast_zsmul, Int.natAbs_of_nonneg hc]
  · simp only [stepDisplacement, hc, decide_false, Bool.false_eq_true, if_false]
    rw [← natCast_zsmul]
    have : (c.natAbs : ℤ) = -c := by omega
    rw [this, smul_neg, neg_smul, neg_neg]
theorem axisPath_eq_append (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by
  simp [axisPath, List.finRange_succ]
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by
  rw [axisPath_eq_append, pathDisplacement_append, pathDisplacement_append, pathDisplacement_append,
    pathDisplacement_replicate_axis, pathDisplacement_replicate_axis, pathDisplacement_replicate_axis]
  simp only [List.append_nil]
  rw [pathDisplacement_replicate_axis, siteOfCoords_eq_sum, ← Equiv.sum_comp π, Fin.sum_univ_four]
  abel
def partialOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by
  by_cases h : m = i
  · subst h
    simp
  · simp [h]
theorem partialOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : partialOffset h π 0 = 0 := by
  funext m
  simp [partialOffset]
theorem partialOffset_succ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    partialOffset h π ((k : ℕ) + 1) = partialOffset h π k + h (π k) • Pi.single (π k) 1 := by
  funext m
  rw [add_smul_single_apply]
  simp only [partialOffset]
  by_cases e : m = π k
  · subst e
    simp
  · have hne : π.symm m ≠ k := fun h' => e (by rw [← h']; simp)
    have hne' : ((π.symm m : Fin 4) : ℕ) ≠ k := fun h' => hne (Fin.ext h')
    simp only [e, if_false, add_zero]
    by_cases hlt : ((π.symm m : Fin 4) : ℕ) < k
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have : ¬ ((π.symm m : Fin 4) : ℕ) < (k : ℕ) + 1 := by omega
      simp [hlt, this]
theorem partialOffset_add_mem_centredCube (L : ℕ) (h : Fin 4 → ℤ) (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (k : Fin 4) (r : ℕ) (hr : r ≤ (h (π k)).natAbs) :
    partialOffset h π k + (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1 ∈
      centredCube L := by
  rw [mem_centredCube_iff_abs_le]
  have hh' := mem_centredCube_iff_abs_le.1 hh
  intro m
  rw [add_smul_single_apply]
  by_cases e : m = π k
  · subst e
    have e0 : partialOffset h π k (π k) = 0 := by simp [partialOffset]
    rw [e0, zero_add]
    simp only [if_true]
    have := hh' (π k)
    have h3 : |(if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ))| = r := by
      split_ifs <;> simp
    rw [h3]
    refine le_trans ?_ this
    have : (r : ℤ) ≤ ((h (π k)).natAbs : ℤ) := by exact_mod_cast hr
    rwa [Int.natCast_natAbs] at this
  · simp only [e, if_false, add_zero, partialOffset]
    split_ifs
    · exact hh' m
    · have := hh' (π 0)
      exact le_trans (by simp) this
theorem pathWithin_axisPath {j : ℕ} {Q : Finset (F.Site j)} (z : F.Site j) {L : ℕ}
    (hQ : ∀ o ∈ centredCube L, z + siteOfCoords j o ∈ Q)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) : PathWithin Q z (axisPath h π) := by
  have piece : ∀ k : Fin 4, PathWithin Q (z + siteOfCoords j (partialOffset h π k))
      (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) := by
    intro k
    refine pathWithin_replicate _ _ _ fun r hr => ?_
    have := hQ _ (partialOffset_add_mem_centredCube L h hh π k r hr)
    rw [siteOfCoords_add, siteOfCoords_single, ← add_assoc] at this
    convert this using 2
    by_cases hc : 0 ≤ h (π k)
    · simp [stepDisplacement, hc]
    · simp [stepDisplacement, hc]
  have step : ∀ k : Fin 4, z + siteOfCoords j (partialOffset h π k) +
      pathDisplacement j (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
        z + siteOfCoords j (partialOffset h π ((k : ℕ) + 1)) := by
    intro k
    rw [partialOffset_succ, siteOfCoords_add, siteOfCoords_single, pathDisplacement_replicate_axis, add_assoc]
  rw [axisPath_eq_append]
  have p0 := piece 0
  have p1 := piece 1
  have p2 := piece 2
  have p3 := piece 3
  have s0 := step 0
  have s1 := step 1
  have s2 := step 2
  have s3 := step 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add] at p0 p1 p2 s0 s1 s2
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [e3] at p3 s3
  rw [partialOffset_zero, siteOfCoords_zero, add_zero] at p0 s0
  simp only [List.append_nil]
  refine pathWithin_append _ _ _ p0 ?_
  rw [s0]
  refine pathWithin_append _ _ _ p1 ?_
  rw [s1]
  refine pathWithin_append _ _ _ p2 ?_
  rw [s2]
  exact p3
end Paths
section Tree
variable {F : BlockFrame}
theorem zero_mem_centredCube (hL : Odd F.blockSide) : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
  rw [mem_centredCube]
  intro i
  have := blockSide_eq_two_mul_halfSide_add_one hL
  have hpos : 0 < F.blockSide := hL.pos
  have : (0 : ℤ) ≤ halfSide F.blockSide := by
    omega
  simp only [Pi.zero_apply]
  omega
theorem mem_sitesOfCells_depth (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (x : F.Site F.depth) : x ∈ sitesOfCells S F.depth ↔ enclosingCell x ∈ S := by
  rw [mem_sitesOfCells]
  have hnt := top_sub_depth F
  simp only [hnt, pow_one]
  constructor
  · rintro ⟨y, hy, o, ho, rfl⟩
    rwa [enclosingCell_cellCentre_add hs hL y o ho]
  · intro h
    exact ⟨_, h, _, (cellOffset_mem_and_eq hs hL x).1, (cellOffset_mem_and_eq hs hL x).2.symm⟩
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite (j := F.depth) y = cellCentre F.depth y := by
  have hnt := top_sub_depth F
  funext i
  simp [refineSite, cellCentre, siteOfCoords, hnt]
theorem axialGauge_cellCentre_add (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (π : Equiv.Perm (Fin 4))
    (W : F.GaugeField F.depth) (y : F.Cell) (o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) :
    axialGauge π W (cellCentre F.depth y + siteOfCoords F.depth o) =
      pathHolonomy W (cellCentre F.depth y) (axisPath o π) := by
  simp only [axialGauge, enclosingCell_cellCentre_add hs hL y o ho, cellOffset_cellCentre_add hs hL y o ho]
theorem axisPath_zero (π : Equiv.Perm (Fin 4)) : axisPath 0 π = [] := by
  simp [axisPath]
theorem axialGauge_cellCentre (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (π : Equiv.Perm (Fin 4))
    (W : F.GaugeField F.depth) (y : F.Cell) : axialGauge π W (cellCentre F.depth y) = 1 := by
  have := axialGauge_cellCentre_add hs hL π W y 0 (zero_mem_centredCube hL)
  rw [siteOfCoords_zero, add_zero, axisPath_zero] at this
  simpa [pathHolonomy] using this
theorem pathHolonomy_gaugeTransform_axisPath (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide)
    (π : Equiv.Perm (Fin 4)) (W : F.GaugeField F.depth) (y : F.Cell) (o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) :
    pathHolonomy (gaugeTransform (axialGauge π W) W) (cellCentre F.depth y) (axisPath o π) = 1 := by
  rw [pathHolonomy_gaugeTransform, pathDisplacement_axisPath, axialGauge_cellCentre hs hL,
    axialGauge_cellCentre_add hs hL π W y o ho]
  simp
def axisSegment (h : Fin 4 → ℤ) (k : Fin 4) : List PathStep :=
  List.replicate (h k).natAbs (k, decide (0 ≤ h k))
theorem axisPath_one_eq (h : Fin 4 → ℤ) :
    axisPath h 1 = axisSegment h 0 ++ (axisSegment h 1 ++ (axisSegment h 2 ++ axisSegment h 3)) := by
  rw [axisPath_eq_append, List.append_nil]
  rfl
theorem axisSegment_add_single_of_ne (o : Fin 4 → ℤ) (i k : Fin 4) (hk : k ≠ i) :
    axisSegment (o + Pi.single i 1) k = axisSegment o k := by
  have e : (o + Pi.single i 1 : Fin 4 → ℤ) k = o k := by simp [hk]
  unfold axisSegment
  rw [e]
theorem axisSegment_of_eq_zero (h : Fin 4 → ℤ) (k : Fin 4) (hz : h k = 0) : axisSegment h k = [] := by
  unfold axisSegment
  rw [hz]
  simp
theorem axisSegment_add_single_of_nonneg (o : Fin 4 → ℤ) (i : Fin 4) (h0 : 0 ≤ o i) :
    axisSegment (o + Pi.single i 1) i = axisSegment o i ++ [(i, true)] := by
  have e : (o + Pi.single i 1 : Fin 4 → ℤ) i = o i + 1 := by simp
  have hn : (o i + 1).natAbs = (o i).natAbs + 1 := by omega
  have d1 : decide (0 ≤ o i + 1) = true := by
    rw [decide_eq_true_eq]; omega
  have d2 : decide (0 ≤ o i) = true := by
    rw [decide_eq_true_eq]; exact h0
  unfold axisSegment
  rw [e, hn, d1, d2, List.replicate_succ']
theorem axisSegment_of_neg (o : Fin 4 → ℤ) (i : Fin 4) (h0 : o i < 0) :
    axisSegment o i = axisSegment (o + Pi.single i 1) i ++ [(i, false)] := by
  have e : (o + Pi.single i 1 : Fin 4 → ℤ) i = o i + 1 := by simp
  have hn : (o i).natAbs = (o i + 1).natAbs + 1 := by omega
  have d2 : decide (0 ≤ o i) = false := by
    rw [decide_eq_false_iff_not]; omega
  unfold axisSegment
  rw [e, hn, d2, List.replicate_succ']
  by_cases h1 : o i + 1 = 0
  · rw [h1]; simp
  · have d1 : decide (0 ≤ o i + 1) = false := by
      rw [decide_eq_false_iff_not]; omega
    rw [d1]
theorem fin_four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide
theorem axisPath_add_single_of_nonneg (o : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → o l = 0) (h0 : 0 ≤ o i) :
    axisPath (o + Pi.single i 1) 1 = axisPath o 1 ++ [(i, true)] := by
  rw [axisPath_one_eq, axisPath_one_eq]
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · rw [axisSegment_add_single_of_nonneg o 0 h0, axisSegment_add_single_of_ne o 0 1 (by decide),
      axisSegment_add_single_of_ne o 0 2 (by decide), axisSegment_add_single_of_ne o 0 3 (by decide),
      axisSegment_of_eq_zero o 1 (hz 1 (by decide)), axisSegment_of_eq_zero o 2 (hz 2 (by decide)),
      axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_add_single_of_nonneg o 1 h0, axisSegment_add_single_of_ne o 1 0 (by decide),
      axisSegment_add_single_of_ne o 1 2 (by decide), axisSegment_add_single_of_ne o 1 3 (by decide),
      axisSegment_of_eq_zero o 2 (hz 2 (by decide)), axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_add_single_of_nonneg o 2 h0, axisSegment_add_single_of_ne o 2 0 (by decide),
      axisSegment_add_single_of_ne o 2 1 (by decide), axisSegment_add_single_of_ne o 2 3 (by decide),
      axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_add_single_of_nonneg o 3 h0, axisSegment_add_single_of_ne o 3 0 (by decide),
      axisSegment_add_single_of_ne o 3 1 (by decide), axisSegment_add_single_of_ne o 3 2 (by decide)]
    simp
theorem axisPath_of_neg (o : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → o l = 0) (h0 : o i < 0) :
    axisPath o 1 = axisPath (o + Pi.single i 1) 1 ++ [(i, false)] := by
  rw [axisPath_one_eq, axisPath_one_eq]
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · rw [axisSegment_of_neg o 0 h0, axisSegment_add_single_of_ne o 0 1 (by decide),
      axisSegment_add_single_of_ne o 0 2 (by decide), axisSegment_add_single_of_ne o 0 3 (by decide),
      axisSegment_of_eq_zero o 1 (hz 1 (by decide)), axisSegment_of_eq_zero o 2 (hz 2 (by decide)),
      axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_of_neg o 1 h0, axisSegment_add_single_of_ne o 1 0 (by decide),
      axisSegment_add_single_of_ne o 1 2 (by decide), axisSegment_add_single_of_ne o 1 3 (by decide),
      axisSegment_of_eq_zero o 2 (hz 2 (by decide)), axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_of_neg o 2 h0, axisSegment_add_single_of_ne o 2 0 (by decide),
      axisSegment_add_single_of_ne o 2 1 (by decide), axisSegment_add_single_of_ne o 2 3 (by decide),
      axisSegment_of_eq_zero o 3 (hz 3 (by decide))]
    simp
  · rw [axisSegment_of_neg o 3 h0, axisSegment_add_single_of_ne o 3 0 (by decide),
      axisSegment_add_single_of_ne o 3 1 (by decide), axisSegment_add_single_of_ne o 3 2 (by decide)]
    simp
theorem cellCentre_add_siteOfCoords_add_unitStep (y : F.Cell) (o : Fin 4 → ℤ) (i : Fin 4) :
    cellCentre F.depth y + siteOfCoords F.depth o + unitStep F.depth i =
      cellCentre F.depth y + siteOfCoords F.depth (o + Pi.single i 1) := by
  rw [siteOfCoords_add, add_assoc]
  rfl
theorem cellCentre_add_unitStep (y : F.Cell) (i : Fin 4) :
    cellCentre F.depth (y + unitStep F.top i) = cellCentre F.depth y + (F.blockSide : ℤ) • unitStep F.depth i := by
  rw [unitStep_eq, cellCentre_add F.depth (Nat.le_succ _)]
  congr 1
  funext k
  simp [siteOfCoords, unitStep, basisVector]
theorem cellCentre_add_siteOfCoords_add_unitStep_crossing (y : F.Cell) (o : Fin 4 → ℤ) (i : Fin 4) :
    cellCentre F.depth y + siteOfCoords F.depth o + unitStep F.depth i =
      cellCentre F.depth (y + unitStep F.top i) +
        siteOfCoords F.depth (o + (1 - (F.blockSide : ℤ)) • Pi.single i 1) := by
  rw [cellCentre_add_unitStep, siteOfCoords_add, siteOfCoords_single, sub_smul, one_smul]
  abel
theorem unitStep_top_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : (unitStep F.top i : F.Cell) ≠ 0 := by
  intro h
  have h1 := congrFun h i
  have h2 : (((1 : ℤ)) : ZMod (F.period F.top i)) = ((0 : ℤ) : ZMod (F.period F.top i)) := by
    simpa [unitStep, siteOfCoords] using h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_top] at h2
  have h3 := Int.le_of_dvd (by omega) (by simpa using h2 : ((F.extent i : ℕ) : ℤ) ∣ 1)
  have := hs i
  omega
theorem cellOffset_lt_of_not_isCrossingBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (x : F.Site F.depth) (i : Fin 4) (h : ¬ IsCrossingBond (x, i)) : cellOffset x i < halfSide F.blockSide := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  set y := enclosingCell x with hy
  set o := cellOffset x with hoo
  by_contra hlt
  have hoi := (mem_centredCube.1 ho i).2
  have heq : o i = halfSide F.blockSide := by omega
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hmem : o + (1 - (F.blockSide : ℤ)) • Pi.single i 1 ∈ centredCube F.blockSide := by
    rw [mem_centredCube]
    intro m
    rw [add_smul_single_apply]
    by_cases e : m = i
    · subst e
      simp only [if_true]
      omega
    · simp only [e, if_false, add_zero]
      exact mem_centredCube.1 ho m
  apply h
  show enclosingCell (x + unitStep F.depth i) ≠ enclosingCell x
  rw [← hy]
  have e1 : x + unitStep F.depth i = cellCentre F.depth (y + unitStep F.top i) +
      siteOfCoords F.depth (o + (1 - (F.blockSide : ℤ)) • Pi.single i 1) := by
    rw [← cellCentre_add_siteOfCoords_add_unitStep_crossing, hx]
  rw [e1, enclosingCell_cellCentre_add hs' hL _ _ hmem]
  intro h2
  exact unitStep_top_ne_zero hs i (by simpa using h2)
theorem gaugeTransform_axialGauge_of_isAxialTreeBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (W : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4)
    (hb : IsAxialTreeBond (x, i)) : gaugeTransform (axialGauge 1 W) W x i = 1 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  set y := enclosingCell x with hy
  set o := cellOffset x with hoo
  have hlt : o i < halfSide F.blockSide := cellOffset_lt_of_not_isCrossingBond hs hL x i hb.1
  have hz : ∀ l, i < l → o l = 0 := hb.2
  have hmem : o + Pi.single i 1 ∈ centredCube F.blockSide := by
    rw [mem_centredCube]
    intro m
    by_cases e : m = i
    · subst e
      have := mem_centredCube.1 ho m
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · have := mem_centredCube.1 ho m
      simpa [e] using this
  have hx' : x + unitStep F.depth i = cellCentre F.depth y + siteOfCoords F.depth (o + Pi.single i 1) := by
    rw [← cellCentre_add_siteOfCoords_add_unitStep, hx]
  set X := gaugeTransform (axialGauge 1 W) W with hX
  have t0 : pathHolonomy X (cellCentre F.depth y) (axisPath o 1) = 1 :=
    pathHolonomy_gaugeTransform_axisPath hs' hL 1 W y o ho
  have t1 : pathHolonomy X (cellCentre F.depth y) (axisPath (o + Pi.single i 1) 1) = 1 :=
    pathHolonomy_gaugeTransform_axisPath hs' hL 1 W y _ hmem
  by_cases h0 : 0 ≤ o i
  · rw [axisPath_add_single_of_nonneg o i hz h0, pathHolonomy_append, t0, pathDisplacement_axisPath, hx] at t1
    simpa [pathHolonomy, linkValue] using t1
  · rw [axisPath_of_neg o i hz (by omega), pathHolonomy_append, t1, pathDisplacement_axisPath, ← hx'] at t0
    simpa [pathHolonomy, linkValue, stepDisplacement] using t0
end Tree
section Units
theorem coe_mul_unitQuaternion (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.1 g.2).1
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.1 g.2).2
theorem norm_coe_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, norm_coe_unitQuaternion, one_mul]
theorem norm_mul_coe (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_coe_unitQuaternion, mul_one]
theorem norm_mul_sub_one_le (a b : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem norm_mul_inv_sub_one (a b : UnitQuaternion) :
    ‖((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - b‖ := by
  have e : ((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 = ((a : ℍ[ℝ]) - b) * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [coe_mul_unitQuaternion, sub_mul, coe_mul_coe_inv]
  rw [e, norm_mul_coe]
theorem norm_inv_mul_sub_one (a b : UnitQuaternion) :
    ‖((a⁻¹ * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - b‖ := by
  have e : ((a⁻¹ * b : UnitQuaternion) : ℍ[ℝ]) - 1 = ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((b : ℍ[ℝ]) - a) := by
    rw [coe_mul_unitQuaternion, mul_sub, coe_inv_mul_coe]
  rw [e, norm_coe_mul, norm_sub_rev]
theorem norm_inv_sub_one (a : UnitQuaternion) : ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem norm_conj_sub_one (a b : UnitQuaternion) :
    ‖((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem norm_mul_mul_sub_le (a x b : UnitQuaternion) :
    ‖((a * x * b : UnitQuaternion) : ℍ[ℝ]) - x‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by
  have e : ((a * x * b : UnitQuaternion) : ℍ[ℝ]) - x =
      ((a : ℍ[ℝ]) * (x : ℍ[ℝ])) * ((b : ℍ[ℝ]) - 1) + ((a : ℍ[ℝ]) - 1) * (x : ℍ[ℝ]) := by
    rw [coe_mul_unitQuaternion, coe_mul_unitQuaternion]; noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [← coe_mul_unitQuaternion, norm_coe_mul, norm_mul_coe]
  linarith
end Units
section Gauged
variable {F : BlockFrame}
theorem pathDisplacement_plaquette (j : ℕ) (μ ν : Fin 4) :
    pathDisplacement (F := F) j [(μ, true), (ν, true), (μ, false), (ν, false)] = 0 := by
  simp [pathDisplacement, stepDisplacement]
theorem plaquetteDefect_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (gaugeTransform γ X) p = plaquetteDefect X p := by
  unfold plaquetteDefect plaquetteHolonomy
  rw [pathHolonomy_gaugeTransform, pathDisplacement_plaquette, add_zero]
  exact norm_conj_sub_one _ _
end Gauged
end GaugeFixing
end YangMills.Construction
end
