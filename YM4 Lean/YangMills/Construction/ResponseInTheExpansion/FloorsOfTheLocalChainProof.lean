import YangMills.Construction.ResponseInTheExpansion.FloorsOfTheLocalChain
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter
namespace YangMills.Construction.ResponseInTheExpansion
namespace LocalChainFloorsAux
private theorem eventually_mul_log_pow_le_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ k ≤ x ^ ε := by
  have h := isLittleO_log_rpow_rpow_atTop (k : ℝ) hε
  have h2 := h.def (c := 1 / (|K| + 1)) (by positivity)
  filter_upwards [h2, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxp : 0 < x ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg hxp.le, Real.rpow_natCast] at hx
  have hlk : 0 ≤ Real.log x ^ k := pow_nonneg hl k
  have h1 : K * Real.log x ^ k ≤ (|K| + 1) * Real.log x ^ k :=
    mul_le_mul_of_nonneg_right ((le_abs_self K).trans (by linarith)) hlk
  refine h1.trans ?_
  have hpos : 0 < |K| + 1 := by positivity
  calc (|K| + 1) * Real.log x ^ k ≤ (|K| + 1) * (1 / (|K| + 1) * x ^ ε) := mul_le_mul_of_nonneg_left hx hpos.le
    _ = x ^ ε := by field_simp
private theorem eventually_mul_rpow_le_rpow {a b : ℝ} (hab : a < b) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * x ^ a ≤ x ^ b := by
  have h := (tendsto_rpow_atTop (sub_pos.2 hab)).eventually (eventually_ge_atTop K)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le a)
private theorem floor_log_cube_le {x : ℝ} (hl : 0 ≤ Real.log x) : (⌊Real.log x ^ 3⌋₊ : ℝ) ≤ Real.log x ^ 3 :=
  Nat.floor_le (pow_nonneg hl 3)
private theorem log_cube_sub_one_le_floor (x : ℝ) : Real.log x ^ 3 - 1 ≤ (⌊Real.log x ^ 3⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one (Real.log x ^ 3)
  linarith
private theorem floor_log_sq_le {x : ℝ} : (⌊Real.log x ^ 2⌋₊ : ℝ) ≤ Real.log x ^ 2 :=
  Nat.floor_le (sq_nonneg _)
private theorem log_sq_sub_one_le_floor (x : ℝ) : Real.log x ^ 2 - 1 ≤ (⌊Real.log x ^ 2⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one (Real.log x ^ 2)
  linarith
end LocalChainFloorsAux
open LocalChainFloorsAux
set_option maxHeartbeats 1000000 in
theorem localChainFloors_holds : localChainFloorsStatement := by
  intro K c hK hc
  have hlog := Real.tendsto_log_atTop
  have hL2 : ∀ᶠ x : ℝ in atTop, max 2 (4 / c) ≤ Real.log x := hlog.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hL2,
    eventually_mul_rpow_le_rpow (a := 1 / 90) (b := 1 / 20) (by norm_num) 480,
    eventually_mul_log_pow_le_rpow 3 (ε := 1 / 20) (by norm_num) 96,
    eventually_mul_rpow_le_rpow (a := 0) (b := 1 / 20) (by norm_num) 99,
    eventually_mul_rpow_le_rpow (a := 1 / 90) (b := 1) (by norm_num) 20,
    eventually_mul_rpow_le_rpow (a := 1 / 5) (b := 1) (by norm_num) K,
    eventually_mul_rpow_le_rpow (a := -1) (b := -(1 / 2 : ℝ) + 1 / 1000) (by norm_num) K,
    eventually_mul_rpow_le_rpow (a := -1) (b := -(1 / 2 : ℝ) + 1 / 1000) (by norm_num) 1,
    eventually_mul_log_pow_le_rpow 3 (ε := 1 / 1000) (by norm_num) 3,
    eventually_mul_log_pow_le_rpow 2 (ε := 1 / 1000) (by norm_num) 3,
    eventually_mul_rpow_le_rpow (a := 0) (b := 1 / 1000) (by norm_num) 12,
    eventually_mul_log_pow_le_rpow 2 (ε := 1) (by norm_num) K]
    with x h1 hl2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have hx0 : 0 < x := by linarith
  set lg := Real.log x with hlg
  have hl2' : 2 ≤ lg := (le_max_left _ _).trans hl2
  have hl4 : 4 / c ≤ lg := (le_max_right _ _).trans hl2
  have hlg0 : 0 ≤ lg := by linarith
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at a3 a4 a5 a10 a11
  have hs1 := log_cube_sub_one_le_floor x
  have hs2 := floor_log_cube_le (x := x) hlg0
  have hd1 := log_sq_sub_one_le_floor x
  have hd2 := floor_log_sq_le (x := x)
  rw [← hlg] at hs1 hs2 hd1 hd2
  have hcube : 8 ≤ lg ^ 3 := by nlinarith [sq_nonneg lg, mul_self_nonneg (lg - 2)]
  have hsq : 4 ≤ lg ^ 2 := by nlinarith
  have hfl := Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 20))
  have hxm2 : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hprod : x * x ^ (-2 : ℝ) = x ^ (-1 : ℝ) := by
    have := Real.rpow_add hx0 1 (-2)
    rw [Real.rpow_one] at this
    rw [← this]
    norm_num
  refine ⟨h1, ?_, ?_, ?_, ?_, a4, a5, ?_, a6, ?_, ?_⟩
  · linarith
  · have : (1 : ℝ) ≤ (⌊lg ^ 2⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  · linarith
  · have hlog2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hM : lg ≤ (⌊lg ^ 2⌋₊ : ℝ) * Real.log 2 := by
      have h0 : (0 : ℝ) ≤ ⌊lg ^ 2⌋₊ := Nat.cast_nonneg _
      have h3 : lg ^ 2 - 1 ≤ (⌊lg ^ 2⌋₊ : ℝ) := hd1
      have : lg ≤ (lg ^ 2 - 1) * 0.69 := by nlinarith
      nlinarith
    have h2 : Real.log x ≤ Real.log (2 ^ ⌊lg ^ 2⌋₊) := by
      rw [Real.log_pow]
      exact hM
    exact (Real.log_le_log_iff hx0 (by positivity)).1 h2
  · have hcl : 4 ≤ c * lg := by
      have := (div_le_iff₀ hc).1 hl4
      linarith
    have hcl2 : 2 * lg ≤ c * (⌊lg ^ 3⌋₊ : ℝ) := by
      have hs : lg ^ 3 / 2 ≤ (⌊lg ^ 3⌋₊ : ℝ) := by linarith
      have h3 : c * (lg ^ 3 / 2) ≤ c * (⌊lg ^ 3⌋₊ : ℝ) := mul_le_mul_of_nonneg_left hs hc.le
      have h4 : 2 * lg ≤ c * (lg ^ 3 / 2) := by
        have e1 : 4 * lg ^ 2 ≤ c * lg * lg ^ 2 := mul_le_mul_of_nonneg_right hcl (sq_nonneg _)
        have e2 : 2 * lg ≤ lg * lg := mul_le_mul_of_nonneg_right hl2' hlg0
        have e3 : c * (lg ^ 3 / 2) = c * lg * lg ^ 2 / 2 := by ring
        have e4 : lg ^ 2 = lg * lg := pow_two lg
        rw [e3]
        linarith
      linarith
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.2 ?_
    rw [← hlg]
    linarith
  · have e3 : 3 * lg ^ 3 ≤ x ^ ((1 : ℝ) / 1000) := a8
    have e2 : 3 * lg ^ 2 ≤ x ^ ((1 : ℝ) / 1000) := a9
    have e1 : 12 ≤ x ^ ((1 : ℝ) / 1000) := a10
    linarith
  · have hd0 : (0 : ℝ) ≤ ⌊lg ^ 2⌋₊ := Nat.cast_nonneg _
    have h5 : K * (⌊lg ^ 2⌋₊ : ℝ) ≤ x := by
      have : K * (⌊lg ^ 2⌋₊ : ℝ) ≤ K * lg ^ 2 := mul_le_mul_of_nonneg_left hd2 hK
      exact this.trans a11
    calc K * (⌊lg ^ 2⌋₊ : ℝ) * x ^ (-2 : ℝ) ≤ x * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right h5 hxm2
      _ = x ^ (-1 : ℝ) := hprod
      _ ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000) := by simpa using a7
end YangMills.Construction.ResponseInTheExpansion
end
