import Mathlib
open Filter
namespace YangMills.ReferenceCalibration

/-- At a stopping torus of side ell*q, the union of the exceptional events
for all sites and plaquettes has probability at most exp(-q). -/
theorem eventually_small_reference_torus_tail
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ell C A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ q : ℝ in atTop, ∀ x : ℝ, q ^ 92 ≤ x → x ≤ A * q ^ 92 →
      (ell * q) ^ 4 * (Real.exp (-(a * x)) +
        16 * Real.exp (C * Real.log x - b * (x / q ^ 32))) ≤ Real.exp (-q) := by
  have hbig (s : ℝ) (hs : 0 < s) (u : ℝ) :
      ∀ᶠ q : ℝ in atTop, u ≤ s * q :=
    (tendsto_id.const_mul_atTop hs).eventually_ge_atTop u
  filter_upwards [eventually_ge_atTop (1 : ℝ), hbig a ha 2,
    hbig b hb (|C| * (|Real.log A| + 92) + 2),
    eventually_ge_atTop (17 * ell ^ 4 * (Nat.factorial 5 : ℝ))] with q hq hqa hqb hsize
  intro x hlow hhigh
  have hqpos : 0 < q := by linarith
  have hq2 : q ^ 2 ≤ x := (pow_le_pow_right₀ hq (by decide : 2 ≤ 92)).trans hlow
  have hx1 : 1 ≤ x := (one_le_pow₀ hq (n := 92)).trans hlow
  have hxq : q ^ 2 ≤ x / q ^ 32 := by
    apply (le_div_iff₀ (pow_pos hqpos 32)).2
    simpa [← pow_add] using (pow_le_pow_right₀ hq (by decide : 2 + 32 ≤ 92)).trans hlow
  have hlog : Real.log x ≤ (|Real.log A| + 92) * q := by
    calc Real.log x ≤ Real.log (A * q ^ 92) := Real.log_le_log (by linarith) hhigh
      _ = Real.log A + 92 * Real.log q := by rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; norm_num
      _ ≤ (|Real.log A| + 92) * q := by
        have := Real.log_le_sub_one_of_pos hqpos
        nlinarith [le_abs_self (Real.log A), mul_le_mul_of_nonneg_left hq (abs_nonneg (Real.log A))]
  have hC : C * Real.log x ≤ |C| * ((|Real.log A| + 92) * q) :=
    mul_le_mul (le_abs_self C) hlog (Real.log_nonneg hx1) (abs_nonneg _)
  have h1 : Real.exp (-(a * x)) ≤ Real.exp (-(2*q)) := Real.exp_le_exp.2 (by
    nlinarith [mul_le_mul_of_nonneg_right hqa hqpos.le, mul_le_mul_of_nonneg_left hq2 ha.le])
  have h2 : Real.exp (C * Real.log x - b * (x / q ^ 32)) ≤ Real.exp (-(2*q)) :=
    Real.exp_le_exp.2 (by
      nlinarith [mul_le_mul_of_nonneg_right hqb hqpos.le, mul_le_mul_of_nonneg_left hxq hb.le])
  have hvol : 17 * (ell * q) ^ 4 ≤ Real.exp q := by
    have hpow := Real.pow_div_factorial_le_exp q hqpos.le 5
    apply le_trans _ hpow
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hsize (pow_nonneg hqpos.le 4)]
  calc _ ≤ (ell * q) ^ 4 * (Real.exp (-(2*q)) + 16 * Real.exp (-(2*q))) := by gcongr
    _ = (17 * (ell * q) ^ 4) * Real.exp (-(2*q)) := by ring
    _ ≤ Real.exp q * Real.exp (-(2*q)) := by gcongr
    _ = Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring

end YangMills.ReferenceCalibration
