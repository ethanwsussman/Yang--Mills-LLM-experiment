import YangMills.Construction.Continuum.TwoFormsOfTheGrowthCondition
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.GrowthForms
open ConfigurationSpace Continuum
private theorem two_pow_le_factorial_add_one (m : ℕ) : (2 : ℝ) ^ m ≤ ((m + 1).factorial : ℝ) := by
  have h : 2 ^ m ≤ (m + 1).factorial := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ (m + 1), pow_succ, mul_comm]
      exact Nat.mul_le_mul (by omega) ih
  exact_mod_cast h
private theorem binaryLog_nonneg {M : ℝ} (hM : 1 ≤ M) : 0 ≤ binaryLog M :=
  div_nonneg (Real.log_nonneg hM) (Real.log_nonneg (by norm_num))
private theorem two_rpow_binaryLog {M : ℝ} (hM : 0 < M) : (2 : ℝ) ^ binaryLog M = M := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), binaryLog, mul_div_cancel₀ _ hlog,
    Real.exp_log hM]
private theorem pow_le_max_mul_factorial_rpow (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    C ^ n ≤ max 1 C * (n.factorial : ℝ) ^ binaryLog (max 1 C) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hM : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hM0 : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos hM
  have hL := binaryLog_nonneg hM
  have hpow : ((2 : ℝ) ^ m) ^ binaryLog (max 1 C) = max 1 C ^ m := by
    rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), two_rpow_binaryLog hM0, Real.rpow_natCast]
  have hle : max 1 C ^ m ≤ ((m + 1).factorial : ℝ) ^ binaryLog (max 1 C) := by
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (two_pow_le_factorial_add_one m) hL
  calc C ^ (m + 1) ≤ max 1 C ^ (m + 1) := pow_le_pow_left₀ hC (le_max_right _ _) _
    _ = max 1 C * max 1 C ^ m := by rw [pow_succ, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hM0.le
theorem growthFormsEquiv_holds : GrowthFormsEquiv := by
  refine ⟨pow_le_max_mul_factorial_rpow, fun S hS => ⟨?_, ?_⟩⟩
  · intro k c C κ hk hc hC hκ hb
    have hM : (1 : ℝ) ≤ max 1 C := le_max_left _ _
    have hM0 : (0 : ℝ) ≤ max 1 C := zero_le_one.trans hM
    have hL := binaryLog_nonneg hM
    refine ⟨hS, hk, mul_nonneg hc hM0, add_nonneg hκ hL,
      fun n => c * C ^ n * (n.factorial : ℝ) ^ κ, ?_, ?_, ?_⟩
    · intro n _
      positivity
    · intro n hn φ
      rw [mul_comm n k]
      exact hb n hn φ
    · intro n hn
      have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      have hκn : (0 : ℝ) ≤ (n.factorial : ℝ) ^ κ := (Real.rpow_pos_of_pos hf _).le
      rw [Real.rpow_add hf]
      calc c * C ^ n * (n.factorial : ℝ) ^ κ
          ≤ c * (max 1 C * (n.factorial : ℝ) ^ binaryLog (max 1 C)) * (n.factorial : ℝ) ^ κ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_max_mul_factorial_rpow C hC n hn) hc) hκn
        _ = _ := by ring
  · rintro s α β ⟨-, -, -, -, c, hc0, hb, hc⟩ n hn φ
    refine (hb n hn φ).trans ?_
    rw [mul_comm n s, one_pow, mul_one]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hc n hn)) _
end YangMills.Construction.GrowthForms
