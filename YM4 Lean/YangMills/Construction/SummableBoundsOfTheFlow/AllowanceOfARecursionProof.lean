import YangMills.Construction.SummableBoundsOfTheFlow.AllowanceOfARecursion
import Mathlib
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open scoped ContDiff
namespace YangMills.Construction.CouplingFlow
namespace RecursionBounds
theorem sub_mul_rpow_neg_five_quarters_le {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (q - p) * q ^ (-(5 / 4) : ℝ) ≤ 4 * (p ^ (-(1 / 4) : ℝ) - q ^ (-(1 / 4) : ℝ)) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  obtain ⟨s, hs0, hs1, rfl⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ p = s * q :=
    ⟨p / q, div_pos hp hq, (div_le_one hq).2 hpq, by field_simp⟩
  have hsp : 1 + (1 - s) / 4 ≤ s ^ (-(1 / 4) : ℝ) := by
    have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : s ^ (-(1 / 4) : ℝ) = Real.exp (Real.log s * (-(1 / 4))) := Real.rpow_def_of_pos hs0 _
    have h3 := Real.add_one_le_exp (Real.log s * (-(1 / 4)))
    rw [h2]; linarith
  have hmul : (s * q) ^ (-(1 / 4) : ℝ) = s ^ (-(1 / 4) : ℝ) * q ^ (-(1 / 4) : ℝ) :=
    Real.mul_rpow hs0.le hq.le
  have hq5 : q ^ (-(5 / 4) : ℝ) * q = q ^ (-(1 / 4) : ℝ) := by
    have h := Real.rpow_add hq (-(5 / 4) : ℝ) 1
    rw [Real.rpow_one] at h
    rw [← h]; norm_num
  have hA : 0 ≤ q ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hq.le _
  rw [hmul, ← hq5]
  have hw : 0 ≤ q ^ (-(5 / 4) : ℝ) * q := mul_nonneg hA hq.le
  have h := mul_nonneg hw (sub_nonneg.2 hsp)
  nlinarith [h]
theorem sub_mul_inv_sq_le {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) : (q - p) * (q ^ 2)⁻¹ ≤ p⁻¹ - q⁻¹ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have h1 : p⁻¹ - q⁻¹ = (q - p) * (p * q)⁻¹ := by field_simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hpq)
  exact inv_anti₀ (mul_pos hp hq) (by nlinarith)
theorem two_rpow_five_quarters_le : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 12 / 5 := by
  have h : ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ 4 = 32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (5 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]; norm_num
  by_contra hc
  have h2 := pow_lt_pow_left₀ (not_le.1 hc) (by norm_num) (n := 4) (by norm_num)
  rw [h] at h2
  norm_num at h2
theorem rpow_neg_quarter_le_of_le {u v : ℝ} (hv : 0 < v) (h : 16 / 81 * v ≤ u) :
    u ^ (-(1 / 4) : ℝ) ≤ 3 / 2 * v ^ (-(1 / 4) : ℝ) := by
  have h0 : 0 < 16 / 81 * v := by positivity
  have h1 : u ^ (-(1 / 4) : ℝ) ≤ (16 / 81 * v) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h0 h (by norm_num)
  have h2 : (16 / 81 * v) ^ (-(1 / 4) : ℝ) = (16 / 81 : ℝ) ^ (-(1 / 4) : ℝ) * v ^ (-(1 / 4) : ℝ) :=
    Real.mul_rpow (by norm_num) hv.le
  have h3 : (16 / 81 : ℝ) ^ (-(1 / 4) : ℝ) = 3 / 2 := by
    have e : (16 / 81 : ℝ) = (2 / 3 : ℝ) ^ ((4 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; norm_num
    rw [e, ← Real.rpow_mul (by norm_num)]
    have : ((4 : ℕ) : ℝ) * (-(1 / 4) : ℝ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]; norm_num
  rw [h2, h3] at h1
  exact h1
structure FloorData (c₀ c M R X Cr : ℝ) : Prop where
  c₀_pos : 0 < c₀
  c_nonneg : 0 ≤ c
  M_nonneg : 0 ≤ M
  R_nonneg : 0 ≤ R
  X_ge : 8 ≤ X
  X_c : 16 * c ≤ X
  X_c₀ : c₀ ≤ X
  X_MR : 128 * (M + R) ≤ c₀ * X
  Cr_def : Cr = 13 * R / c₀
  Cr_X : 8 * Cr * X ^ (-(1 / 4) : ℝ) ≤ 1
variable {b d x : ℕ → ℝ} {c₀ c M R X Cr : ℝ}
theorem FloorData.Cr_nonneg (h : FloorData c₀ c M R X Cr) : 0 ≤ Cr := by
  rw [h.Cr_def]; exact div_nonneg (by linarith [h.R_nonneg]) h.c₀_pos.le
theorem FloorData.X_pos (h : FloorData c₀ c M R X Cr) : 0 < X := by linarith [h.X_ge]
theorem FloorData.corrections_le (h : FloorData c₀ c M R X Cr) {v : ℝ} (hv : X ≤ v) :
    M / v + R * v ^ (-(5 / 4) : ℝ) ≤ c₀ / 4 := by
  have hv0 : 0 < v := lt_of_lt_of_le h.X_pos hv
  have hv1 : 1 ≤ v := by linarith [h.X_ge]
  have h1 : v ^ (-(5 / 4) : ℝ) ≤ v⁻¹ := by
    rw [← Real.rpow_neg_one v]
    exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  have h2 : R * v ^ (-(5 / 4) : ℝ) ≤ R * v⁻¹ := mul_le_mul_of_nonneg_left h1 h.R_nonneg
  have h3 : (M + R) * v⁻¹ ≤ c₀ / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hv0]
    have hMR : 0 ≤ M + R := add_nonneg h.M_nonneg h.R_nonneg
    nlinarith [h.X_MR, h.c₀_pos, mul_le_mul_of_nonneg_left hv h.c₀_pos.le]
  have h4 : M / v = M * v⁻¹ := div_eq_mul_inv _ _
  rw [h4]; nlinarith
theorem sub_eq_sum_steps (i j : ℕ) (hij : i ≤ j) :
    x i - x j = ∑ l ∈ Ico i j, (b l + (d l / x l - stepRemainder b d x l)) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [sum_Ico_succ_top hj, ← ih]
    unfold stepRemainder
    ring
theorem drop_two_sided_of (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {t : ℕ} (hx : StaysAbove X x t)
    (hf : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ t) :
    3 / 4 * c₀ * ((j : ℝ) - i) - 2 * c ≤ x i - x j ∧ x i - x j ≤ 5 / 4 * c₀ * ((j : ℝ) - i) + 2 * c := by
  have hsum := sub_eq_sum_steps (b := b) (d := d) (x := x) i j hij
  rw [sum_add_distrib] at hsum
  have hsl := abs_le.1 (hs i j hij)
  have hsm : ∀ l ∈ Ico i j, |d l / x l - stepRemainder b d x l| ≤ c₀ / 4 := by
    intro l hl
    have hlj := (mem_Ico.1 hl).2
    have hlt : l < t := lt_of_lt_of_le hlj hj
    have hX := hx l hlt.le
    have hx0 : 0 < x l := lt_of_lt_of_le h.X_pos hX
    have h1 : |d l / x l| ≤ M / x l := by
      rw [abs_div, abs_of_pos hx0]
      exact div_le_div_of_nonneg_right (hd l) hx0.le
    calc |d l / x l - stepRemainder b d x l| ≤ |d l / x l| + |stepRemainder b d x l| := abs_sub _ _
      _ ≤ M / x l + R * x l ^ (-(5 / 4) : ℝ) := add_le_add h1 (hf l hlt)
      _ ≤ c₀ / 4 := h.corrections_le hX
  have hcard : ((Ico i j).card : ℝ) = (j : ℝ) - i := by
    rw [Nat.card_Ico, Nat.cast_sub hij]
  have hab : |∑ l ∈ Ico i j, (d l / x l - stepRemainder b d x l)| ≤ ((j : ℝ) - i) * (c₀ / 4) := by
    calc _ ≤ ∑ l ∈ Ico i j, |d l / x l - stepRemainder b d x l| := abs_sum_le_sum_abs _ _
      _ ≤ (Ico i j).card • (c₀ / 4) := sum_le_card_nsmul _ _ _ hsm
      _ = ((j : ℝ) - i) * (c₀ / 4) := by rw [nsmul_eq_mul, hcard]
  have hab' := abs_le.1 hab
  constructor <;> nlinarith [hsl.1, hsl.2, hab'.1, hab'.2]
theorem half_le_of (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c) {t : ℕ}
    (hx : StaysAbove X x t) (hf : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ))
    {l : ℕ} (hl : l ≤ t) : (x t + 3 / 4 * c₀ * ((t : ℝ) - l)) / 2 ≤ x l := by
  have h1 := (drop_two_sided_of h hd hs hx hf hl le_rfl).1
  have h2 := hx t le_rfl
  have h3 : (0 : ℝ) ≤ (t : ℝ) - l := by
    have : (l : ℝ) ≤ t := by exact_mod_cast hl
    linarith
  have h4 : 0 ≤ 3 / 4 * c₀ * ((t : ℝ) - l) := mul_nonneg (by linarith [h.c₀_pos]) h3
  linarith [h.X_c, h.c_nonneg]
theorem sum_abs_stepRemainder_le (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M)
    (hs : HasAverageSlope b c₀ c) {t : ℕ}
    (hx : StaysAbove X x t) (hf : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) :
    ∑ l ∈ range t, |stepRemainder b d x l| ≤ Cr * x t ^ (-(1 / 4) : ℝ) := by
  have hc := h.c₀_pos
  have hxt : 0 < x t := lt_of_lt_of_le h.X_pos (hx t le_rfl)
  set e : ℝ := 3 / 4 * c₀ with he
  have he0 : 0 < e := by positivity
  set G : ℕ → ℝ := fun l => (x t + e * ((t : ℝ) - l)) ^ (-(1 / 4) : ℝ) with hG
  have key : ∀ l ∈ range t, |stepRemainder b d x l| ≤ (R * (12 / 5) * (4 / e)) * (G (l + 1) - G l) := by
    intro l hl
    have hlt : l < t := mem_range.1 hl
    have hlr : ((l : ℝ) + 1) ≤ t := by exact_mod_cast hlt
    set p : ℝ := x t + e * ((t : ℝ) - (l + 1)) with hp
    set q : ℝ := x t + e * ((t : ℝ) - l) with hq
    have hp0 : 0 < p := by
      have : 0 ≤ e * ((t : ℝ) - (l + 1)) := mul_nonneg he0.le (by linarith)
      linarith
    have hqp : q - p = e := by rw [hp, hq]; ring
    have hpq : p ≤ q := by linarith
    have hq0 : 0 < q := by linarith
    have hstep := sub_mul_rpow_neg_five_quarters_le hp0 hpq
    rw [hqp] at hstep
    have hlow := half_le_of h hd hs hx hf hlt.le
    have hlow' : q / 2 ≤ x l := hlow
    have h1 : x l ^ (-(5 / 4) : ℝ) ≤ (q / 2) ^ (-(5 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlow' (by norm_num)
    have h2 : (q / 2) ^ (-(5 / 4) : ℝ) = q ^ (-(5 / 4) : ℝ) * (2 : ℝ) ^ (5 / 4 : ℝ) := by
      have e2 : ((2 : ℝ)⁻¹) ^ (-(5 / 4) : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
        rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      rw [div_eq_mul_inv, Real.mul_rpow hq0.le (by norm_num), e2]
    have hA : 0 ≤ q ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hq0.le _
    have h3 : x l ^ (-(5 / 4) : ℝ) ≤ q ^ (-(5 / 4) : ℝ) * (12 / 5) := by
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left two_rpow_five_quarters_le hA)
    have h4 : q ^ (-(5 / 4) : ℝ) ≤ 4 / e * (G (l + 1) - G l) := by
      have hGl : G (l + 1) = p ^ (-(1 / 4) : ℝ) := by
        simp only [hG, hp]; push_cast; rfl
      have hGl' : G l = q ^ (-(1 / 4) : ℝ) := rfl
      rw [hGl, hGl', div_mul_eq_mul_div, le_div_iff₀ he0]
      linarith
    calc |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ) := hf l hlt
      _ ≤ R * (q ^ (-(5 / 4) : ℝ) * (12 / 5)) := mul_le_mul_of_nonneg_left h3 h.R_nonneg
      _ ≤ R * ((4 / e * (G (l + 1) - G l)) * (12 / 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (by norm_num)) h.R_nonneg
      _ = (R * (12 / 5) * (4 / e)) * (G (l + 1) - G l) := by ring
  have hsum := sum_le_sum key
  rw [← mul_sum, sum_range_sub] at hsum
  have hG0 : 0 ≤ G 0 := by
    refine Real.rpow_nonneg ?_ _
    have : (0 : ℝ) ≤ (t : ℝ) - ((0 : ℕ) : ℝ) := by simp
    have := mul_nonneg he0.le this
    linarith
  have hGt : G t = x t ^ (-(1 / 4) : ℝ) := by simp [hG]
  have hcoef : R * (12 / 5) * (4 / e) ≤ Cr := by
    rw [h.Cr_def, he]
    have : R * (12 / 5) * (4 / (3 / 4 * c₀)) = (64 / 5 * R) / c₀ := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith [h.R_nonneg]) hc.le
  have hpos : 0 ≤ x t ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hxt.le _
  have hcoef0 : 0 ≤ R * (12 / 5) * (4 / e) := by
    have := h.R_nonneg
    positivity
  calc _ ≤ (R * (12 / 5) * (4 / e)) * (G t - G 0) := hsum
    _ ≤ (R * (12 / 5) * (4 / e)) * x t ^ (-(1 / 4) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef0
        rw [hGt]; linarith
    _ ≤ Cr * x t ^ (-(1 / 4) : ℝ) := mul_le_mul_of_nonneg_right hcoef hpos
theorem sum_inv_sq_le (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {t : ℕ} (hx : StaysAbove X x t)
    (hf : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) :
    ∑ l ∈ range t, (x l ^ 2)⁻¹ ≤ 16 / (3 * c₀ * x t) := by
  have hc := h.c₀_pos
  have hxt : 0 < x t := lt_of_lt_of_le h.X_pos (hx t le_rfl)
  set e : ℝ := 3 / 4 * c₀ with he
  have he0 : 0 < e := by positivity
  set G : ℕ → ℝ := fun l => (x t + e * ((t : ℝ) - l))⁻¹ with hG
  have key : ∀ l ∈ range t, (x l ^ 2)⁻¹ ≤ (4 / e) * (G (l + 1) - G l) := by
    intro l hl
    have hlt : l < t := mem_range.1 hl
    have hlr : ((l : ℝ) + 1) ≤ t := by exact_mod_cast hlt
    set p : ℝ := x t + e * ((t : ℝ) - (l + 1)) with hp
    set q : ℝ := x t + e * ((t : ℝ) - l) with hq
    have hp0 : 0 < p := by
      have : 0 ≤ e * ((t : ℝ) - (l + 1)) := mul_nonneg he0.le (by linarith)
      linarith
    have hqp : q - p = e := by rw [hp, hq]; ring
    have hpq : p ≤ q := by linarith
    have hq0 : 0 < q := by linarith
    have hstep := sub_mul_inv_sq_le hp0 hpq
    rw [hqp] at hstep
    have hlow : q / 2 ≤ x l := half_le_of h hd hs hx hf hlt.le
    have h1 : (x l ^ 2)⁻¹ ≤ ((q / 2) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hlow 2)
    have h2 : ((q / 2) ^ 2)⁻¹ = 4 * (q ^ 2)⁻¹ := by field_simp; norm_num
    have hGl : G (l + 1) = p⁻¹ := by
      simp only [hG, hp]; push_cast; rfl
    have hGl' : G l = q⁻¹ := rfl
    rw [hGl, hGl']
    have h3 : (q ^ 2)⁻¹ ≤ (p⁻¹ - q⁻¹) / e := by
      rw [le_div_iff₀ he0]; linarith
    calc (x l ^ 2)⁻¹ ≤ 4 * (q ^ 2)⁻¹ := h2 ▸ h1
      _ ≤ 4 * ((p⁻¹ - q⁻¹) / e) := by linarith
      _ = 4 / e * (p⁻¹ - q⁻¹) := by ring
  have hsum := sum_le_sum key
  rw [← mul_sum, sum_range_sub] at hsum
  have hG0 : 0 ≤ G 0 := by
    refine inv_nonneg.2 ?_
    have : (0 : ℝ) ≤ (t : ℝ) - ((0 : ℕ) : ℝ) := by simp
    have := mul_nonneg he0.le this
    linarith
  have hGt : G t = (x t)⁻¹ := by simp [hG]
  have h4e : 0 ≤ 4 / e := by positivity
  calc _ ≤ (4 / e) * (G t - G 0) := hsum
    _ ≤ (4 / e) * (x t)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ h4e
        rw [hGt]; linarith
    _ = 16 / (3 * c₀ * x t) := by rw [he]; field_simp; norm_num
theorem exp_le_two_of_le {u : ℝ} (hu : u ≤ 1 / 8) : Real.exp u ≤ 2 := by
  have h : (1 / 8 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc Real.exp u ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (hu.trans h)
    _ = 2 := Real.exp_log (by norm_num)
theorem FloorData.M_le (h : FloorData c₀ c M R X Cr) {v : ℝ} (hv : X ≤ v) : 128 * M ≤ c₀ * v := by
  have h1 := mul_le_mul_of_nonneg_left hv h.c₀_pos.le
  nlinarith [h.X_MR, h.R_nonneg]
theorem sum_inv_sq_small (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {t : ℕ} (hx : StaysAbove X x t)
    (hf : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) :
    2 * M * ∑ l ∈ range t, (x l ^ 2)⁻¹ ≤ 1 / 12 := by
  have hc := h.c₀_pos
  have hX := hx t le_rfl
  have hxt : 0 < x t := lt_of_lt_of_le h.X_pos hX
  have h1 := sum_inv_sq_le h hd hs hx hf
  have h2 : 2 * M * ∑ l ∈ range t, (x l ^ 2)⁻¹ ≤ 2 * M * (16 / (3 * c₀ * x t)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith [h.M_nonneg])
  refine h2.trans ?_
  have h3 := h.M_le hX
  have : 2 * M * (16 / (3 * c₀ * x t)) = (32 * M) / (3 * (c₀ * x t)) := by field_simp; ring
  rw [this, div_le_iff₀ (by positivity)]
  linarith
theorem FloorData.inv_sq_small (h : FloorData c₀ c M R X Cr) {v : ℝ} (hv : X ≤ v) :
    2 * M * (v ^ 2)⁻¹ ≤ 1 / 64 := by
  have hv0 : 0 < v := lt_of_lt_of_le h.X_pos hv
  have h3 := h.M_le hv
  have h4 : c₀ * v ≤ v ^ 2 := by
    have : c₀ ≤ v := h.X_c₀.trans hv
    nlinarith
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  linarith
theorem FloorData.R_le (h : FloorData c₀ c M R X Cr) {v : ℝ} (hv : X ≤ v) :
    R * v ^ (-(5 / 4) : ℝ) ≤ Cr * v ^ (-(1 / 4) : ℝ) := by
  have hv0 : 0 < v := lt_of_lt_of_le h.X_pos hv
  have hq5 : v ^ (-(5 / 4) : ℝ) * v = v ^ (-(1 / 4) : ℝ) := by
    have e := Real.rpow_add hv0 (-(5 / 4) : ℝ) 1
    rw [Real.rpow_one] at e
    rw [← e]; norm_num
  have hA : 0 ≤ v ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hv0.le _
  rw [← hq5]
  have hR : R ≤ Cr * v := by
    rw [h.Cr_def, div_mul_eq_mul_div, le_div_iff₀ h.c₀_pos]
    have := h.X_c₀.trans hv
    nlinarith [h.R_nonneg, h.c₀_pos, mul_le_mul_of_nonneg_left this h.R_nonneg]
  nlinarith [mul_le_mul_of_nonneg_right hR hA]
theorem FloorData.quarter_small (h : FloorData c₀ c M R X Cr) {v : ℝ} (hv : X ≤ v) :
    8 * Cr * v ^ (-(1 / 4) : ℝ) ≤ 1 := by
  have h1 : v ^ (-(1 / 4) : ℝ) ≤ X ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h.X_pos hv (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith [h.Cr_nonneg] : (0 : ℝ) ≤ 8 * Cr)
  exact h2.trans h.Cr_X
theorem abs_sub_flow_le (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {t : ℕ} (hx : StaysAbove X x t)
    (hf : ∀ l ≤ t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) :
    ∀ l, l ≤ t + 1 →
      |x l - flow b d (x 0) l| ≤
        Real.exp (2 * M * ∑ j ∈ range l, (x j ^ 2)⁻¹) * ∑ j ∈ range l, |stepRemainder b d x j| ∧
      |x l - flow b d (x 0) l| ≤ 1 / 2 := by
  intro l
  induction l with
  | zero => intro _; simp [flow]
  | succ l ih =>
    intro hl
    have hlt : l ≤ t := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hX := hx l hlt
    have hx0 : 0 < x l := lt_of_lt_of_le h.X_pos hX
    have hx8 : 8 ≤ x l := h.X_ge.trans hX
    obtain ⟨y, hy⟩ : ∃ y, y = flow b d (x 0) l := ⟨_, rfl⟩
    rw [← hy] at ih1 ih2
    have hyl : x l / 2 ≤ y := by
      have := (abs_le.1 ih2).2
      linarith
    have hy0 : 0 < y := by linarith
    have hrec : x (l + 1) - flow b d (x 0) (l + 1) =
        (x l - y) * (1 + d l / (x l * y)) + stepRemainder b d x l := by
      have e1 : flow b d (x 0) (l + 1) = y - b l - d l / y := by rw [hy]; rfl
      rw [e1]
      unfold stepRemainder
      field_simp
      ring
    have hu : |d l / (x l * y)| ≤ 2 * M * (x l ^ 2)⁻¹ := by
      rw [abs_div, abs_of_pos (mul_pos hx0 hy0), div_le_iff₀ (mul_pos hx0 hy0)]
      have e : 2 * M * (x l ^ 2)⁻¹ * (x l * y) = M * (2 * y / x l) := by field_simp
      have e2 : 1 ≤ 2 * y / x l := by rw [le_div_iff₀ hx0]; linarith
      rw [e]
      nlinarith [hd l, h.M_nonneg]
    set E := Real.exp (2 * M * (x l ^ 2)⁻¹) with hE
    have h1E : 1 ≤ E := Real.one_le_exp (by have := h.M_nonneg; positivity)
    have hfac : |1 + d l / (x l * y)| ≤ E := by
      calc |1 + d l / (x l * y)| ≤ 1 + |d l / (x l * y)| := by
            simpa using abs_add_le 1 (d l / (x l * y))
        _ ≤ Real.exp |d l / (x l * y)| := by linarith [Real.add_one_le_exp |d l / (x l * y)|]
        _ ≤ E := Real.exp_le_exp.2 hu
    set P := Real.exp (2 * M * ∑ j ∈ range l, (x j ^ 2)⁻¹) with hP
    set S := ∑ j ∈ range l, |stepRemainder b d x j| with hS
    have hP1 : 1 ≤ P := Real.one_le_exp (by
      have := h.M_nonneg
      have : 0 ≤ ∑ j ∈ range l, (x j ^ 2)⁻¹ := sum_nonneg fun j _ => by positivity
      positivity)
    have hP' : Real.exp (2 * M * ∑ j ∈ range (l + 1), (x j ^ 2)⁻¹) = P * E := by
      rw [sum_range_succ, mul_add, Real.exp_add]
    have hS' : ∑ j ∈ range (l + 1), |stepRemainder b d x j| = S + |stepRemainder b d x l| :=
      sum_range_succ _ _
    have hmain : |x (l + 1) - flow b d (x 0) (l + 1)| ≤ (P * E) * (S + |stepRemainder b d x l|) := by
      rw [hrec]
      have hPE : 1 ≤ P * E := by nlinarith
      calc |(x l - y) * (1 + d l / (x l * y)) + stepRemainder b d x l|
          ≤ |x l - y| * |1 + d l / (x l * y)| + |stepRemainder b d x l| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (P * S) * E + |stepRemainder b d x l| := by
            have := mul_le_mul ih1 hfac (abs_nonneg _) (by positivity)
            linarith
        _ ≤ (P * E) * (S + |stepRemainder b d x l|) := by
            nlinarith [abs_nonneg (stepRemainder b d x l)]
    refine ⟨by rw [hP', hS']; exact hmain, hmain.trans ?_⟩
    have hx' : StaysAbove X x l := fun j hj => hx j (hj.trans hlt)
    have hf' : ∀ j < l, |stepRemainder b d x j| ≤ R * x j ^ (-(5 / 4) : ℝ) :=
      fun j hj => hf j (hj.le.trans hlt)
    have hsq := sum_inv_sq_small h hd hs hx' hf'
    have hsq2 := h.inv_sq_small hX
    have hPE2 : P * E ≤ 2 := by
      rw [← hP']
      apply exp_le_two_of_le
      rw [sum_range_succ, mul_add]
      linarith
    have hSl := sum_abs_stepRemainder_le h hd hs hx' hf'
    have hq := h.quarter_small hX
    have hr : |stepRemainder b d x l| ≤ Cr * x l ^ (-(1 / 4) : ℝ) := (hf l hlt).trans (h.R_le hX)
    have hSS0 : 0 ≤ S + |stepRemainder b d x l| := by positivity
    nlinarith
theorem boundsUpTo_of (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {mw : ℕ} (hmw : 8 * (c + 1) / c₀ ≤ mw) {t : ℕ} (hx : StaysAbove X x t)
    (hf : ∀ l ≤ t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) :
    BoundsUpTo b d c₀ c M R Cr mw x t := by
  have hc := h.c₀_pos
  have hf' : ∀ l < t, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ) := fun l hl => hf l hl.le
  have hnear := abs_sub_flow_le h hd hs hx hf
  refine ⟨fun i j hij hj => drop_two_sided_of h hd hs hx hf' hij hj, ?_, ?_,
    sum_abs_stepRemainder_le h hd hs hx hf', sum_inv_sq_le h hd hs hx hf', ?_, ?_,
    (hnear (t + 1) le_rfl).2⟩
  · intro i m hm him
    have h1 := (drop_two_sided_of h hd hs hx hf' (Nat.le_add_right i m) him).1
    have h2 : (((i + m : ℕ) : ℝ) - i) = m := by push_cast; ring
    rw [h2] at h1
    have h3 : 8 * (c + 1) / c₀ ≤ m := hmw.trans (by exact_mod_cast hm)
    rw [div_le_iff₀ hc] at h3
    nlinarith
  · intro l hl
    have hX := hx l hl
    have hx0 : 0 < x l := lt_of_lt_of_le h.X_pos hX
    have h1 : |d l / x l| ≤ M / x l := by
      rw [abs_div, abs_of_pos hx0]
      exact div_le_div_of_nonneg_right (hd l) hx0.le
    have h2 := abs_le.1 h1
    have h3 := abs_le.1 (hf l hl)
    have h4 : x l - x (l + 1) = b l + d l / x l - stepRemainder b d x l := by
      unfold stepRemainder; ring
    rw [h4]
    linarith [h2.1, h3.2]
  · intro l hl
    have h1 := (hnear l (by omega)).2
    have h2 := (abs_le.1 h1).2
    have h3 := h.X_ge.trans (hx l hl)
    linarith
  · have h1 := (hnear t (by omega)).1
    have hsq := sum_inv_sq_small h hd hs hx hf'
    have hP : Real.exp (2 * M * ∑ j ∈ range t, (x j ^ 2)⁻¹) ≤ 2 := exp_le_two_of_le (by linarith)
    have hS := sum_abs_stepRemainder_le h hd hs hx hf'
    have hS0 : 0 ≤ ∑ j ∈ range t, |stepRemainder b d x j| := sum_nonneg fun j _ => abs_nonneg _
    calc _ ≤ _ := h1
      _ ≤ 2 * ∑ j ∈ range t, |stepRemainder b d x j| := mul_le_mul_of_nonneg_right hP hS0
      _ ≤ 2 * (Cr * x t ^ (-(1 / 4) : ℝ)) := by linarith
      _ = 2 * Cr * x t ^ (-(1 / 4) : ℝ) := by ring
theorem stepRemainder_flow (β : ℝ) (l : ℕ) : stepRemainder b d (flow b d β) l = 0 := by
  unfold stepRemainder
  exact sub_self _
theorem flow_hasDerivAt (β : ℝ) : ∀ l, (∀ j < l, flow b d β j ≠ 0) →
    HasDerivAt (fun β' => flow b d β' l) (∏ j ∈ range l, (1 + d j / flow b d β j ^ 2)) β := by
  intro l
  induction l with
  | zero =>
    intro _
    rw [prod_range_zero]
    exact hasDerivAt_id' β
  | succ l ih =>
    intro hne
    have h := ih fun j hj => hne j (Nat.lt_succ_of_lt hj)
    have hy := hne l (Nat.lt_succ_self l)
    have h2 := (h.sub_const (b l)).sub ((hasDerivAt_const β (d l)).div h hy)
    rw [prod_range_succ]
    refine HasDerivAt.congr_deriv h2 ?_
    field_simp
    ring
theorem flow_contDiffAt (β : ℝ) : ∀ l, (∀ j < l, flow b d β j ≠ 0) →
    ContDiffAt ℝ ∞ (fun β' => flow b d β' l) β := by
  intro l
  induction l with
  | zero => intro _; exact contDiffAt_id
  | succ l ih =>
    intro hne
    have h := ih fun j hj => hne j (Nat.lt_succ_of_lt hj)
    have hy := hne l (Nat.lt_succ_self l)
    exact (h.sub contDiffAt_const).sub (contDiffAt_const.div h hy)
theorem flow_tendsto : ∀ l, Tendsto (fun β => flow b d β l) atTop atTop := by
  intro l
  induction l with
  | zero => exact tendsto_id
  | succ l ih =>
    have h1 : Tendsto (fun β => -b l - d l / flow b d β l) atTop (𝓝 (-b l - 0)) :=
      tendsto_const_nhds.sub (ih.const_div_atTop (d l))
    refine (ih.atTop_add h1).congr fun β => ?_
    show flow b d β l + (-b l - d l / flow b d β l) = flow b d β l - b l - d l / flow b d β l
    ring
theorem exp_le_prod_one_add (u v : ℕ → ℝ) : ∀ l, (∀ j < l, |u j| ≤ v j) → (∀ j < l, v j ≤ 1 / 2) →
    Real.exp (-2 * ∑ j ∈ range l, v j) ≤ ∏ j ∈ range l, (1 + u j) ∧
      ∏ j ∈ range l, (1 + u j) ≤ Real.exp (∑ j ∈ range l, v j) := by
  intro l
  induction l with
  | zero => intro _ _; simp
  | succ l ih =>
    intro hu hv
    obtain ⟨i1, i2⟩ :=
      ih (fun j hj => hu j (Nat.lt_succ_of_lt hj)) (fun j hj => hv j (Nat.lt_succ_of_lt hj))
    have hul := abs_le.1 (hu l (Nat.lt_succ_self l))
    have hvl := hv l (Nat.lt_succ_self l)
    have a1 : Real.exp (-2 * v l) ≤ 1 + u l := by
      have e1 : 1 + 2 * v l ≤ Real.exp (2 * v l) := by linarith [Real.add_one_le_exp (2 * v l)]
      have e2 : Real.exp (-2 * v l) = (Real.exp (2 * v l))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      have e3 : (Real.exp (2 * v l))⁻¹ ≤ (1 + 2 * v l)⁻¹ := inv_anti₀ (by linarith) e1
      have e4 : (1 + 2 * v l)⁻¹ ≤ 1 - v l := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith
      rw [e2]
      linarith
    have a2 : 1 + u l ≤ Real.exp (v l) := by linarith [Real.add_one_le_exp (v l)]
    rw [prod_range_succ, sum_range_succ, mul_add, Real.exp_add, Real.exp_add]
    have hp0 : 0 ≤ ∏ j ∈ range l, (1 + u j) := (Real.exp_pos _).le.trans i1
    have h10 : 0 ≤ 1 + u l := (Real.exp_pos _).le.trans a1
    constructor
    · have e : -2 * v l = -2 * v l := rfl
      exact mul_le_mul i1 (by simpa using a1) (Real.exp_pos _).le hp0
    · exact mul_le_mul i2 a2 h10 (Real.exp_pos _).le
theorem flow_staysAbove (h : FloorData c₀ c M R X Cr) {β : ℝ} {t : ℕ}
    (hy : ∀ l ≤ t, X + 1 ≤ flow b d β l) :
    StaysAbove X (flow b d β) t ∧
      ∀ l ≤ t, |stepRemainder b d (flow b d β) l| ≤ R * flow b d β l ^ (-(5 / 4) : ℝ) := by
  refine ⟨fun l hl => by linarith [hy l hl], fun l hl => ?_⟩
  rw [stepRemainder_flow, abs_zero]
  have := hy l hl
  exact mul_nonneg h.R_nonneg (Real.rpow_nonneg (by linarith [h.X_ge]) _)
theorem deriv_flow_mem (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {β : ℝ} {t : ℕ} (hy : ∀ l ≤ t, X + 1 ≤ flow b d β l) :
    1 / 2 ≤ deriv (fun β' => flow b d β' t) β ∧ deriv (fun β' => flow b d β' t) β ≤ 2 := by
  have hX1 := h.X_ge
  obtain ⟨hst, hfo⟩ := flow_staysAbove h hy
  have hne : ∀ j < t, flow b d β j ≠ 0 := fun j hj =>
    (show (0 : ℝ) < flow b d β j by linarith [hy j hj.le]).ne'
  rw [(flow_hasDerivAt β t hne).deriv]
  have hsq := sum_inv_sq_small h hd hs hst fun l hl => hfo l hl.le
  have hpb := exp_le_prod_one_add (fun j => d j / flow b d β j ^ 2) (fun j => M * (flow b d β j ^ 2)⁻¹) t
    (fun j hj => by
      have hh : 0 ≤ (flow b d β j ^ 2)⁻¹ := by positivity
      rw [abs_div, div_eq_mul_inv, abs_of_nonneg (sq_nonneg (flow b d β j))]
      exact mul_le_mul_of_nonneg_right (hd j) hh)
    (fun j hj => by
      have := h.inv_sq_small (v := flow b d β j) (by linarith [hy j hj.le])
      linarith)
  have hT : ∑ j ∈ range t, M * (flow b d β j ^ 2)⁻¹ = M * ∑ j ∈ range t, (flow b d β j ^ 2)⁻¹ :=
    (mul_sum _ _ _).symm
  rw [hT] at hpb
  constructor
  · refine le_trans ?_ hpb.1
    have e1 : Real.exp (2 * (M * ∑ j ∈ range t, (flow b d β j ^ 2)⁻¹)) ≤ 2 :=
      exp_le_two_of_le (by linarith)
    have e2 : Real.exp (-2 * (M * ∑ j ∈ range t, (flow b d β j ^ 2)⁻¹)) =
        (Real.exp (2 * (M * ∑ j ∈ range t, (flow b d β j ^ 2)⁻¹)))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [e2, one_div]
    exact inv_anti₀ (Real.exp_pos _) e1
  · exact hpb.2.trans (exp_le_two_of_le (by
      have : 0 ≤ M * ∑ j ∈ range t, (flow b d β j ^ 2)⁻¹ := mul_nonneg h.M_nonneg
        (sum_nonneg fun j _ => by positivity)
      linarith))
theorem step_strictMono (h : FloorData c₀ c M R X Cr) {D B u w : ℝ} (hD : |D| ≤ M) (hu : X + 1 ≤ u)
    (huw : u < w) : u - B - D / u < w - B - D / w := by
  have hX := h.X_ge
  have hu0 : 0 < u := by linarith
  have hw0 : 0 < w := by linarith
  have e : (w - B - D / w) - (u - B - D / u) = (w - u) * (1 + D / (u * w)) := by
    field_simp
    ring
  have hsmall : |D / (u * w)| < 1 := by
    rw [abs_div, abs_of_pos (mul_pos hu0 hw0), div_lt_one (mul_pos hu0 hw0)]
    have h1 := h.M_le (v := u) (by linarith)
    have h2 : c₀ ≤ u := h.X_c₀.trans (by linarith)
    have h3 : u ≤ u * w := by nlinarith
    nlinarith [h.c₀_pos]
  have hpos : 0 < 1 + D / (u * w) := by linarith [(abs_lt.1 hsmall).1]
  have := mul_pos (sub_pos.2 huw) hpos
  linarith
theorem exists_Ici_eq (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) : ∀ t : ℕ, ∃ β₀ : ℝ,
    {β | ∀ l ≤ t, X + 1 ≤ flow b d β l} = Set.Ici β₀ ∧
      StrictMonoOn (fun β => flow b d β t) (Set.Ici β₀) ∧ ∃ l ≤ t, flow b d β₀ l = X + 1 := by
  have hX := h.X_ge
  intro t
  induction t with
  | zero =>
    refine ⟨X + 1, ?_, fun _ _ _ _ hlt => hlt, 0, le_rfl, rfl⟩
    ext β
    constructor
    · intro hh
      exact hh 0 le_rfl
    · intro hh l hl
      obtain rfl : l = 0 := by omega
      exact hh
  | succ t ih =>
    obtain ⟨β₁, hS, hmono, l₀, hl₀, hbind⟩ := ih
    have mem : ∀ β, β₁ ≤ β → ∀ l ≤ t, X + 1 ≤ flow b d β l := by
      intro β hβ
      have : β ∈ {β | ∀ l ≤ t, X + 1 ≤ flow b d β l} := by rw [hS]; exact hβ
      exact this
    have fmono : StrictMonoOn (fun β => flow b d β (t + 1)) (Set.Ici β₁) := by
      intro β hβ β' hβ' hlt
      exact step_strictMono h (hd t) (mem β hβ t le_rfl) (hmono hβ hβ' hlt)
    have fcont : ContinuousOn (fun β => flow b d β (t + 1)) (Set.Ici β₁) := by
      intro β hβ
      refine (flow_hasDerivAt β (t + 1) fun j hj => ?_).continuousAt.continuousWithinAt
      have := mem β hβ j (by omega)
      exact (show (0 : ℝ) < flow b d β j by linarith).ne'
    by_cases hc : X + 1 ≤ flow b d β₁ (t + 1)
    · refine ⟨β₁, ?_, fmono, l₀, by omega, hbind⟩
      ext β
      constructor
      · intro hh
        have : β ∈ {β | ∀ l ≤ t, X + 1 ≤ flow b d β l} := fun l hl => hh l (by omega)
        rw [hS] at this
        exact this
      · intro hb l hl
        rcases Nat.lt_or_ge t l with hlt | hge
        · obtain rfl : l = t + 1 := by omega
          exact hc.trans (fmono.monotoneOn Set.self_mem_Ici hb hb)
        · exact mem β hb l hge
    · have hc := not_le.1 hc
      obtain ⟨B, hB1, hB2⟩ : ∃ B, X + 1 ≤ flow b d B (t + 1) ∧ β₁ ≤ B :=
        (((flow_tendsto (t + 1)).eventually_ge_atTop (X + 1)).and (eventually_ge_atTop β₁)).exists
      have hivt := intermediate_value_Icc hB2 (fcont.mono Set.Icc_subset_Ici_self)
      obtain ⟨β₂, hβ₂, hf₂⟩ := hivt (⟨hc.le, hB1⟩ : X + 1 ∈ Set.Icc _ _)
      have hf₂' : flow b d β₂ (t + 1) = X + 1 := hf₂
      refine ⟨β₂, ?_, fmono.mono (Set.Ici_subset_Ici.2 hβ₂.1), t + 1, le_rfl, hf₂'⟩
      have hm₂ : β₂ ∈ Set.Ici β₁ := hβ₂.1
      ext β
      constructor
      · intro hh
        have h1 : β ∈ {β | ∀ l ≤ t, X + 1 ≤ flow b d β l} := fun l hl => hh l (by omega)
        rw [hS] at h1
        have h2 : flow b d β₂ (t + 1) ≤ flow b d β (t + 1) := by rw [hf₂']; exact hh _ le_rfl
        exact (fmono.le_iff_le hm₂ h1).1 h2
      · intro hb l hl
        have hb' : β₁ ≤ β := hβ₂.1.trans hb
        rcases Nat.lt_or_ge t l with hlt | hge
        · obtain rfl : l = t + 1 := by omega
          rw [← hf₂']
          exact fmono.monotoneOn hm₂ hb' hb
        · exact mem β hb' l hge
theorem flowAbove_of (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c) :
    FlowAbove b d X (X + 2 * c + 1) := by
  have hX := h.X_ge
  constructor
  · intro t
    obtain ⟨β₀, hS, hmono, -⟩ := exists_Ici_eq h hd t
    refine ⟨β₀, hS, hmono, fun β hβ => ?_⟩
    have hy : ∀ l ≤ t, X + 1 ≤ flow b d β l := by
      have : β ∈ {β | ∀ l ≤ t, X + 1 ≤ flow b d β l} := by rw [hS]; exact hβ
      exact this
    refine ⟨flow_contDiffAt β t fun j hj => ?_, deriv_flow_mem h hd hs hy⟩
    exact (show (0 : ℝ) < flow b d β j by linarith [hy j hj.le]).ne'
  · intro K v hv
    obtain ⟨β₀, hS, hmono, l₀, hl₀, hbind⟩ := exists_Ici_eq (b := b) h hd K
    have mem : ∀ β, β₀ ≤ β → ∀ l ≤ K, X + 1 ≤ flow b d β l := by
      intro β hβ
      have : β ∈ {β | ∀ l ≤ K, X + 1 ≤ flow b d β l} := by rw [hS]; exact hβ
      exact this
    obtain ⟨hst, hfo⟩ := flow_staysAbove h (mem β₀ le_rfl)
    have hline := (drop_two_sided_of h hd hs hst (fun l hl => hfo l hl.le) hl₀ le_rfl).1
    have hlow : flow b d β₀ K ≤ v := by
      have h1 : (0 : ℝ) ≤ (K : ℝ) - l₀ := by
        have : (l₀ : ℝ) ≤ K := by exact_mod_cast hl₀
        linarith
      have h2 : 0 ≤ 3 / 4 * c₀ * ((K : ℝ) - l₀) := mul_nonneg (by linarith [h.c₀_pos]) h1
      rw [hbind] at hline
      linarith
    obtain ⟨B, hB1, hB2⟩ : ∃ B, v ≤ flow b d B K ∧ β₀ ≤ B :=
      (((flow_tendsto K).eventually_ge_atTop v).and (eventually_ge_atTop β₀)).exists
    have fcont : ContinuousOn (fun β => flow b d β K) (Set.Icc β₀ B) := by
      intro β hβ
      refine (flow_hasDerivAt β K fun j hj => ?_).continuousAt.continuousWithinAt
      have := mem β hβ.1 j hj.le
      exact (show (0 : ℝ) < flow b d β j by linarith).ne'
    obtain ⟨β, hβ, hfv⟩ := intermediate_value_Icc hB2 fcont (⟨hlow, hB1⟩ : v ∈ Set.Icc _ _)
    have hfv' : flow b d β K = v := hfv
    refine ⟨β, ⟨hfv', mem β hβ.1⟩, ?_⟩
    rintro β' ⟨hv', hfl⟩
    have hm' : β' ∈ Set.Ici β₀ := by
      have : β' ∈ {β | ∀ l ≤ K, X + 1 ≤ flow b d β l} := hfl
      rw [hS] at this
      exact this
    exact hmono.injOn hm' hβ.1 (hv'.trans hfv'.symm)
theorem staysAbove_of_flow (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M)
    (hs : HasAverageSlope b c₀ c) {mw : ℕ}
    (hmw : 8 * (c + 1) / c₀ ≤ mw) (hF : FollowsFlowAbove b d R X x) :
    ∀ t, (∀ l ≤ t, X + 1 ≤ flow b d (x 0) l) → StaysAbove X x t := by
  intro t
  induction t with
  | zero =>
    intro hy l hl
    obtain rfl : l = 0 := by omega
    have := hy 0 le_rfl
    have e : flow b d (x 0) 0 = x 0 := rfl
    rw [e] at this
    linarith
  | succ t ih =>
    intro hy l hl
    have hst := ih fun j hj => hy j (by omega)
    rcases Nat.lt_or_ge t l with hlt | hge
    · obtain rfl : l = t + 1 := by omega
      have hB : BoundsUpTo b d c₀ c M R Cr mw x t :=
        boundsUpTo_of h hd hs hmw hst fun l hl => hF l fun j hj => hst j (hj.trans hl)
      have h1 := (abs_le.1 hB.near_flow_succ).1
      have h2 := hy (t + 1) le_rfl
      linarith
    · exact hst l hge
theorem flowBounds_of (h : FloorData c₀ c M R X Cr) (hd : ∀ l, |d l| ≤ M) (hs : HasAverageSlope b c₀ c)
    {mw : ℕ} (hmw : 8 * (c + 1) / c₀ ≤ mw) (hF : FollowsFlowAbove b d R X x) :
    FlowBounds b d c₀ c M R X Cr mw (X + 2 * c + 1) x := by
  have hX := h.X_ge
  have hc0 := h.c_nonneg
  have hCr := h.Cr_nonneg
  have hB : ∀ t, StaysAbove X x t → BoundsUpTo b d c₀ c M R Cr mw x t := fun t hst =>
    boundsUpTo_of h hd hs hmw hst fun l hl => hF l fun j hj => hst j (hj.trans hl)
  have hfl := staysAbove_of_flow (Cr := Cr) h hd hs hmw hF
  have compare : ∀ {u v : ℝ}, 0 < v → 16 / 81 * v ≤ u →
      2 * Cr * u ^ (-(1 / 4) : ℝ) ≤ 3 * Cr * v ^ (-(1 / 4) : ℝ) := by
    intro u v hv hu
    have := mul_le_mul_of_nonneg_left (rpow_neg_quarter_le_of_le hv hu) (by linarith : (0 : ℝ) ≤ 2 * Cr)
    linarith
  refine ⟨hB, hfl, ?_, ?_⟩
  · intro K v hv hy hfloor
    have hst := hfl K hfloor
    have hn := (hB K hst).near_flow
    rw [hy] at hn
    have hq := h.quarter_small (hst K le_rfl)
    have h1 := (abs_le.1 hn).1
    have hvl : v - 1 / 2 ≤ x K := by linarith
    refine ⟨hvl, hn, compare (by linarith) ?_⟩
    linarith
  · intro K g hg hst hgx
    have hn := (hB K hst).near_flow
    have hxK := h.X_ge.trans (hst K le_rfl)
    have hg2 : 0 < (g ^ 2)⁻¹ := by positivity
    have h1 := abs_le.1 hgx
    have h2 := compare (u := x K) hg2 (by linarith [h1.1, h1.2])
    have h3 : ((g ^ 2)⁻¹) ^ (-(1 / 4) : ℝ) = g ^ (1 / 2 : ℝ) := by
      rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
        ← Real.rpow_natCast g 2, ← Real.rpow_mul hg.le]
      norm_num
    rw [h3] at h2
    exact hn.trans h2
end RecursionBounds
open RecursionBounds in
theorem marginOfRecursionHolds : AllowanceOfRecursionHolds := by
  intro b d c₀ c M R yp hc hM hR hd hs
  have hc0 : 0 ≤ c := by
    have := hs 0 0 le_rfl
    have h2 := (abs_nonneg _).trans this
    linarith
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = 13 * R / c₀ := ⟨_, rfl⟩
  have hCr0 : 0 ≤ Cr := by rw [hCr]; positivity
  obtain ⟨X, hXd⟩ : ∃ X, X = 2 * |yp| + 8 + 16 * c + c₀ + 128 * (M + R) / c₀ + (8 * Cr) ^ 4 :=
    ⟨_, rfl⟩
  have a1 : 0 ≤ |yp| := abs_nonneg _
  have a2 : 0 ≤ 128 * (M + R) / c₀ := by positivity
  have a3 : 0 ≤ (8 * Cr) ^ 4 := by positivity
  have hXpos : 0 < X := by rw [hXd]; positivity
  have hdraw : FloorData c₀ c M R X Cr := by
    refine ⟨hc, hc0, hM, hR, ?_, ?_, ?_, ?_, hCr, ?_⟩
    · rw [hXd]; linarith
    · rw [hXd]; linarith
    · rw [hXd]; linarith
    · have e : c₀ * (128 * (M + R) / c₀) = 128 * (M + R) := by field_simp
      have e2 : 128 * (M + R) / c₀ ≤ X := by rw [hXd]; linarith
      have := mul_le_mul_of_nonneg_left e2 hc.le
      linarith
    · by_cases hA : Cr = 0
      · rw [hA]; norm_num
      · have hA0 : 0 < 8 * Cr := by
          have : 0 < Cr := lt_of_le_of_ne hCr0 (Ne.symm hA)
          positivity
        have h1 : (8 * Cr) ^ 4 ≤ X := by rw [hXd]; linarith
        have h2 : X ^ (-(1 / 4) : ℝ) ≤ ((8 * Cr) ^ 4) ^ (-(1 / 4) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
        have h3 : ((8 * Cr) ^ 4) ^ (-(1 / 4) : ℝ) = (8 * Cr)⁻¹ := by
          rw [← Real.rpow_natCast (8 * Cr) 4, ← Real.rpow_mul hA0.le]
          have : ((4 : ℕ) : ℝ) * (-(1 / 4) : ℝ) = -1 := by norm_num
          rw [this, Real.rpow_neg_one]
        rw [h3] at h2
        have := mul_le_mul_of_nonneg_left h2 hA0.le
        rwa [mul_inv_cancel₀ hA0.ne'] at this
  have hmw : 8 * (c + 1) / c₀ ≤ (⌈8 * (c + 1) / c₀⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨X, Cr, X + 2 * c + 1, ⌈8 * (c + 1) / c₀⌉₊, ?_, hdraw.X_ge, hCr0, hdraw.Cr_X, ?_,
    by linarith, flowAbove_of hdraw hd hs, fun x hF => flowBounds_of hdraw hd hs hmw hF⟩
  · rw [hXd]; linarith [le_abs_self yp]
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
end YangMills.Construction.CouplingFlow
end
