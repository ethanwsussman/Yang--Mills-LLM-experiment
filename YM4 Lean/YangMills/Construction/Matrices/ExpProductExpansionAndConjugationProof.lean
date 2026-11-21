import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChartProof
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.ExpProductExpansionAndConjugation
import Mathlib
open scoped Matrix.Norms.L2Operator Nat
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem hasSum_pow_div_factorial_exp (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (k ! : ℝ)) (Real.exp x) := by apply _root_.YangMills.Construction.BlockAverages.ChartFit.hasSum_pow_div_factorial <;> assumption
private theorem norm_matExp_sub_partial_sum_le (Y : ComplexMatrix2) (n : ℕ) :
    ‖matExp Y - ∑ k ∈ Finset.range n, ((k ! : ℂ)⁻¹) • Y ^ k‖ ≤
      Real.exp ‖Y‖ - ∑ k ∈ Finset.range n, ‖Y‖ ^ k / (k ! : ℝ) := by
  have hY : HasSum (fun k : ℕ => ((k ! : ℂ)⁻¹) • Y ^ k) (matExp Y) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have hY' := (hasSum_nat_add_iff' n).mpr hY
  have hr' := (hasSum_nat_add_iff' n).mpr (hasSum_pow_div_factorial_exp ‖Y‖)
  refine hY'.norm_le_of_bounded hr' fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by positivity)
private theorem exp_sub_partial_sum_le_pow_mul_exp (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    Real.exp x - ∑ k ∈ Finset.range m, x ^ k / (k ! : ℝ) ≤
      x ^ m / (m ! : ℝ) * Real.exp x := by
  have htail := (hasSum_nat_add_iff' m).mpr (hasSum_pow_div_factorial_exp x)
  have hscaled := (hasSum_pow_div_factorial_exp x).mul_left (x ^ m / (m ! : ℝ))
  refine hasSum_le (fun k => ?_) htail hscaled
  have hf : ((m ! : ℝ) * (k ! : ℝ)) ≤ ((k + m)! : ℝ) := by
    have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add k m)
    have hcast : (k ! * m ! : ℝ) ≤ ((k + m)! : ℝ) := by exact_mod_cast this
    linarith [mul_comm (m ! : ℝ) (k ! : ℝ)]
  have hp : (0 : ℝ) < (m ! : ℝ) * (k ! : ℝ) := by positivity
  rw [div_mul_div_comm, pow_add, mul_comm (x ^ k)]
  exact div_le_div_of_nonneg_left (by positivity) hp hf
private theorem mul_expansion_bounds (E Y H P s Q : ComplexMatrix2) (b : ℝ)
    (hH : ‖H‖ ≤ ‖Y‖ ^ 2 / 2)
    (hE0 : ‖E‖ ≤ Real.exp ‖Y‖)
    (hE1 : ‖E - 1‖ ≤ Real.exp ‖Y‖ - 1)
    (hE2 : ‖E - 1 - Y‖ ≤ Real.exp ‖Y‖ - 1 - ‖Y‖)
    (hE3 : ‖E - 1 - Y - H‖ ≤ Real.exp ‖Y‖ - 1 - ‖Y‖ - 1 / 2 * ‖Y‖ ^ 2)
    (hP0 : ‖P‖ ≤ Real.exp b)
    (hP1 : ‖P - 1‖ ≤ Real.exp b - 1)
    (hP2 : ‖P - 1 - s‖ ≤ Real.exp b - 1 - b)
    (hP3 : ‖P - 1 - s - Q‖ ≤ Real.exp b - 1 - b - 1 / 2 * b ^ 2) :
    ‖E * P‖ ≤ Real.exp (‖Y‖ + b) ∧
    ‖E * P - 1‖ ≤ Real.exp (‖Y‖ + b) - 1 ∧
    ‖E * P - 1 - (Y + s)‖ ≤ Real.exp (‖Y‖ + b) - 1 - (‖Y‖ + b) ∧
    ‖E * P - 1 - (Y + s) - (H + Y * s + Q)‖ ≤
      Real.exp (‖Y‖ + b) - 1 - (‖Y‖ + b) - 1 / 2 * (‖Y‖ + b) ^ 2 := by
  rw [Real.exp_add]
  refine ⟨norm_mul_le_of_le hE0 hP0, ?_, ?_, ?_⟩
  · have hsplit : E * P - 1 = (E - 1) * P + (P - 1) := by noncomm_ring
    rw [hsplit]
    have := norm_mul_le_of_le hE1 hP0
    have := norm_add_le ((E - 1) * P) (P - 1)
    nlinarith
  · have hsplit : E * P - 1 - (Y + s) = (E - 1 - Y) * P + (P - 1 - s) + Y * (P - 1) := by
      noncomm_ring
    rw [hsplit]
    have h1 := norm_mul_le_of_le hE2 hP0
    have h2 := norm_mul_le_of_le (le_refl ‖Y‖) hP1
    have h3 := norm_add₃_le (a := (E - 1 - Y) * P) (b := P - 1 - s) (c := Y * (P - 1))
    nlinarith
  · have hsplit : E * P - 1 - (Y + s) - (H + Y * s + Q) =
        (E - 1 - Y - H) * P + (P - 1 - s - Q) + Y * (P - 1 - s) + H * (P - 1) := by
      noncomm_ring
    rw [hsplit]
    have h1 := norm_mul_le_of_le hE3 hP0
    have h2 := norm_mul_le_of_le (le_refl ‖Y‖) hP2
    have h3 := norm_mul_le_of_le hH hP1
    have h4 := norm_add_le ((E - 1 - Y - H) * P + (P - 1 - s - Q) + Y * (P - 1 - s)) (H * (P - 1))
    have h5 := norm_add₃_le (a := (E - 1 - Y - H) * P) (b := P - 1 - s - Q)
      (c := Y * (P - 1 - s))
    nlinarith
private theorem halfCommutatorSum_fin_succ {r : ℕ} (Y : Fin (r + 1) → ComplexMatrix2) :
    halfCommutatorSum Y =
      (1 / 2 : ℂ) • (Y 0 * (∑ i : Fin r, Y i.succ) - (∑ i : Fin r, Y i.succ) * Y 0) +
        halfCommutatorSum fun i : Fin r => Y i.succ := by
  unfold halfCommutatorSum
  rw [Fin.sum_univ_succ, smul_add]
  congr 2
  · have hI : Finset.Ioi (0 : Fin (r + 1)) = Finset.univ.map (Fin.succEmb r) := by
      ext i
      cases i using Fin.cases <;> simp
    rw [hI, Finset.sum_map]
    simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.map_succEmb_Ioi, Finset.sum_map]
    rfl
private theorem half_sq_add_commutator_rearrange (A B C : ComplexMatrix2) :
    (1 / 2 : ℂ) • (A + B) ^ 2 + ((1 / 2 : ℂ) • (A * B - B * A) + C) =
      (1 / 2 : ℂ) • A ^ 2 + A * B + ((1 / 2 : ℂ) • B ^ 2 + C) := by
  simp only [pow_two, add_mul, mul_add]
  module
private theorem prod_matExp_expansion_bounds (r : ℕ) (Y : Fin r → ComplexMatrix2) :
    ‖(List.ofFn fun i => matExp (Y i)).prod‖ ≤ Real.exp (∑ i, ‖Y i‖) ∧
    ‖(List.ofFn fun i => matExp (Y i)).prod - 1‖ ≤ Real.exp (∑ i, ‖Y i‖) - 1 ∧
    ‖(List.ofFn fun i => matExp (Y i)).prod - 1 - ∑ i, Y i‖ ≤
      Real.exp (∑ i, ‖Y i‖) - 1 - ∑ i, ‖Y i‖ ∧
    ‖(List.ofFn fun i => matExp (Y i)).prod - 1 - ∑ i, Y i -
        ((1 / 2 : ℂ) • (∑ i, Y i) ^ 2 + halfCommutatorSum Y)‖ ≤
      Real.exp (∑ i, ‖Y i‖) - 1 - (∑ i, ‖Y i‖) - 1 / 2 * (∑ i, ‖Y i‖) ^ 2 := by
  induction r with
  | zero => simp [halfCommutatorSum]
  | succ r ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih fun i => Y i.succ
    have t0 := norm_matExp_sub_partial_sum_le (Y 0) 0
    have t1 := norm_matExp_sub_partial_sum_le (Y 0) 1
    have t2 := norm_matExp_sub_partial_sum_le (Y 0) 2
    have t3 := norm_matExp_sub_partial_sum_le (Y 0) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, inv_one, one_smul, zero_add, sub_zero,
      div_one, mul_one, Nat.succ_eq_add_one, Nat.reduceAdd] at t0 t1 t2 t3
    have hH : ‖(1 / 2 : ℂ) • Y 0 ^ 2‖ ≤ ‖Y 0‖ ^ 2 / 2 := by
      rw [norm_smul]
      have := norm_pow_le (Y 0) 2
      norm_num
      linarith
    have key := mul_expansion_bounds (matExp (Y 0)) (Y 0) ((1 / 2 : ℂ) • Y 0 ^ 2)
      (List.ofFn fun i : Fin r => matExp (Y i.succ)).prod (∑ i : Fin r, Y i.succ)
      ((1 / 2 : ℂ) • (∑ i : Fin r, Y i.succ) ^ 2 + halfCommutatorSum fun i : Fin r => Y i.succ)
      (∑ i : Fin r, ‖Y i.succ‖) hH t0
      (by simpa using t1)
      (by simpa [sub_sub] using t2)
      (by
        have hrw : matExp (Y 0) - 1 - Y 0 - (1 / 2 : ℂ) • Y 0 ^ 2 =
            matExp (Y 0) - (1 + Y 0 + (2 : ℂ)⁻¹ • Y 0 ^ 2) := by
          rw [one_div]
          abel
        rw [hrw]
        linarith) h0 h1 h2 h3
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ (f := fun i => ‖Y i‖),
      Fin.sum_univ_succ (f := Y), halfCommutatorSum_fin_succ, half_sq_add_commutator_rearrange]
    exact key
private theorem operatorNorm_conj_sub_le_of_near_one (h : ExpLogEstimates) (V Y : ComplexMatrix2)
    (hV : operatorNorm (V - 1) ≤ 1 / 4) :
    operatorNorm (V * Y * V⁻¹ - Y) ≤ 3 * operatorNorm (V - 1) * operatorNorm Y := by
  obtain ⟨-, -, -, h4, -⟩ := h
  have hV' : ‖V - 1‖ ≤ 1 / 4 := hV
  obtain ⟨-, -, hu, hinv, -⟩ := h4 (V - 1) (lt_of_le_of_lt hV' (by norm_num))
  have hsum : 1 + (V - 1) = V := by abel
  rw [hsum] at hu hinv
  have hVi : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hu)
  have hq : ‖V - 1‖ / (1 - ‖V - 1‖) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hb : ‖V⁻¹‖ ≤ 4 / 3 := by
    have h1 : ‖V⁻¹‖ ≤ ‖V⁻¹ - 1‖ + ‖(1 : ComplexMatrix2)‖ := by
      simpa using norm_add_le (V⁻¹ - 1) (1 : ComplexMatrix2)
    rw [norm_one] at h1
    linarith
  have hid : V * Y * V⁻¹ - Y = ((V - 1) * Y - Y * (V - 1)) * V⁻¹ := by
    have h2 : ((V - 1) * Y - Y * (V - 1)) * V⁻¹ = V * Y * V⁻¹ - Y * (V * V⁻¹) := by noncomm_ring
    rw [h2, hVi, mul_one]
  have hc : ‖(V - 1) * Y - Y * (V - 1)‖ ≤ 2 * ‖V - 1‖ * ‖Y‖ := by
    have h3 := norm_sub_le ((V - 1) * Y) (Y * (V - 1))
    have h4 := norm_mul_le (V - 1) Y
    have h5 := norm_mul_le Y (V - 1)
    nlinarith
  show ‖V * Y * V⁻¹ - Y‖ ≤ 3 * ‖V - 1‖ * ‖Y‖
  rw [hid]
  have h6 := norm_mul_le_of_le hc hb
  have h7 : 0 ≤ ‖V - 1‖ * ‖Y‖ := by positivity
  nlinarith
private theorem operatorNorm_conj_matExp_sub_le (h : ExpLogEstimates) (Z Y : ComplexMatrix2) :
    operatorNorm (matExp Z * Y * matExp (-Z) - Y) ≤
      (Real.exp (2 * operatorNorm Z) - 1) * operatorNorm Y := by
  obtain ⟨a0, a1⟩ := h.1 Z
  obtain ⟨b0, b1⟩ := h.1 (-Z)
  show ‖matExp Z * Y * matExp (-Z) - Y‖ ≤ (Real.exp (2 * ‖Z‖) - 1) * ‖Y‖
  simp only [operatorNorm, norm_neg] at a0 a1 b0 b1
  have hsplit : matExp Z * Y * matExp (-Z) - Y =
      (matExp Z - 1) * Y * matExp (-Z) + Y * (matExp (-Z) - 1) := by
    noncomm_ring
  have htwo : Real.exp (2 * ‖Z‖) = Real.exp ‖Z‖ * Real.exp ‖Z‖ := by
    rw [two_mul, Real.exp_add]
  rw [hsplit, htwo]
  have h1 := norm_mul_le_of_le (norm_mul_le_of_le a1 (le_refl ‖Y‖)) b0
  have h2 := norm_mul_le_of_le (le_refl ‖Y‖) b1
  have h3 := norm_add_le ((matExp Z - 1) * Y * matExp (-Z)) (Y * (matExp (-Z) - 1))
  nlinarith
theorem expProductExpansionAndConjugation_holds (h : ExpLogEstimates) :
    ExpProductExpansionAndConjugation := by
  refine ⟨?_, operatorNorm_conj_sub_le_of_near_one h, operatorNorm_conj_matExp_sub_le h⟩
  rintro r Y σ s c P rfl rfl rfl rfl
  obtain ⟨-, -, h2, h3⟩ := prod_matExp_expansion_bounds r Y
  have hσ : 0 ≤ ∑ i, operatorNorm (Y i) := Finset.sum_nonneg fun i _ => norm_nonneg _
  have u2 := exp_sub_partial_sum_le_pow_mul_exp _ hσ 2
  have u3 := exp_sub_partial_sum_le_pow_mul_exp _ hσ 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_mul, Nat.cast_ofNat, pow_zero, pow_one, zero_add, div_one, mul_one,
    Nat.succ_eq_add_one, Nat.reduceAdd] at u2 u3
  refine ⟨h2, ?_, ?_, ?_⟩
  · linarith
  · rw [sub_sub (_ - _ - _)]
    exact h3
  · linarith
end YangMills.Construction.Matrices.ComplexMatrix2
