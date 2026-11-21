import YangMills.ContinuumLimit.StoppedTorusTail
import YangMills.ContinuumLimit.ResponseAtSmallCurvature
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace YangMills.Formulation
open Construction.TorusLumps

/-- The bad-event term and the separation error vanish uniformly in the
stopping window. Here q measures separation and ell*q is the torus side. -/
theorem eventually_small_stopped_errors (ell B C D E c A ε : ℝ) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hc : 0 < c) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∀ᶠ q : ℝ in atTop, ∀ x : ℝ, 1 ≤ x → x ≤ A*q^92 → (clusterRange x : ℝ) ≤ q →
      ((B+1)*(ell*q)^4)^2 * (1 + (D*(clusterRange x:ℝ)^4 * Real.log x)^4) * Real.exp (-q/2) +
      C * Real.exp (-(c * (6/5*q))) * (2*(E*(clusterRange x:ℝ)^4*Real.log x)^2) ≤ ε := by
  let H := |Real.log A| + 92
  let K := ((B+1)*ell^4)^2 * (1+(D*H)^4)
  let J := 2*C*(E*H)^2
  have b (n : ℕ) (c : ℝ) (hc : 0 < c) : Tendsto (fun q : ℝ => q^n * Real.exp (-c*q)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) c hc)
  have ht : Tendsto (fun q : ℝ => K * (q^28 * Real.exp (-(1/2)*q)) +
      J * (q^10*Real.exp (-(c*(6/5))*q))) atTop (𝓝 0) := by
    simpa using ((b 28 (1/2) (by norm_num)).const_mul K).add
      ((b 10 (c*(6/5)) (mul_pos hc (by norm_num))).const_mul J)
  filter_upwards [ht.eventually_le_const hε, eventually_ge_atTop (1:ℝ)] with q hsmall hq
  intro x hx hupper hr
  have hq0 := zero_lt_one.trans_le hq
  have hx0 := zero_lt_one.trans_le hx
  have hA0 := zero_lt_one.trans_le hA
  have H0 : 0 ≤ H := by dsimp [H]; positivity
  have hl : Real.log x ≤ H*q := calc
    _ ≤ Real.log (A*q^92) := Real.log_le_log hx0 hupper
    _ = Real.log A + 92 * Real.log q := by rw [Real.log_mul hA0.ne' (pow_pos hq0 _).ne', Real.log_pow]; norm_num
    _ ≤ H*q := by
      dsimp [H]
      nlinarith [le_abs_self (Real.log A), Real.log_le_sub_one_of_pos hq0, mul_nonneg (abs_nonneg (Real.log A)) (sub_nonneg.mpr hq)]
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have sc (D : ℝ) (hD : 0 ≤ D) : D*(clusterRange x : ℝ)^4*Real.log x ≤ D*H*q^5 := calc
    _ ≤ D*q^4*(H*q) := by gcongr
    _ = _ := by ring
  have hs (D : ℝ) (hD : 0 ≤ D) : 0 ≤ D*(clusterRange x : ℝ)^4*Real.log x :=
    mul_nonneg (mul_nonneg hD (by positivity)) (Real.log_nonneg hx)
  have hD4 := pow_le_pow_left₀ (hs D hD) (sc D hD) 4
  have hE2 := pow_le_pow_left₀ (hs E hE) (sc E hE) 2
  have h1 : 1+(D*(clusterRange x:ℝ)^4 * Real.log x)^4 ≤ (1+(D*H)^4)*q^20 := by
    have h20 := one_le_pow₀ hq (n:=20)
    nlinarith [hD4]
  have h2 : (E*(clusterRange x:ℝ)^4*Real.log x)^2 ≤ (E*H)^2*q^10 := by
    calc _ ≤ _ := hE2
         _ = _ := by ring
  refine le_trans ?_ hsmall
  apply add_le_add
  · calc _ ≤ ((B+1)*(ell*q)^4)^2 * ((1+(D*H)^4)*q^20) * Real.exp (-q/2) := by gcongr
         _ = _ := by dsimp [K]; rw [show -(1/2:ℝ)*q = -q/2 by ring]; ring
  · calc _ ≤ C * Real.exp (-(c*(6/5*q))) * (2*((E*H)^2*q^10)) := by gcongr
         _ = _ := by dsimp [J]; rw [show -(c*(6/5:ℝ))*q = -(c*(6/5*q)) by ring]; ring

end YangMills.Formulation

