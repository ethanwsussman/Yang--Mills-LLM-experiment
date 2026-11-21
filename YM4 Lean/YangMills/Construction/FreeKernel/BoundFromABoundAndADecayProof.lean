import YangMills.Construction.FreeKernel.BoundFromABoundAndADecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.FourDimKernel
theorem boundFromBoundAndDecay_holds : BoundFromBoundAndDecay := by
  intro n y X c₀ c hy hX hc₀ hc hXc₀ hdecay
  have hw : 0 < bracketOnePlus y := by
    unfold bracketOnePlus
    linarith
  have hwn : 0 < bracketOnePlus y ^ n := pow_pos hw n
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [Real.rpow_neg hw.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hwn]
  rcases le_total y 1 with h | h
  · have hw2 : bracketOnePlus y ≤ 2 := by
      unfold bracketOnePlus
      linarith
    have hpow : bracketOnePlus y ^ n ≤ 2 ^ n := pow_le_pow_left₀ hw.le hw2 n
    have hXM : X ≤ max c₀ c := le_max_of_le_left hXc₀
    calc X * bracketOnePlus y ^ n ≤ max c₀ c * 2 ^ n := mul_le_mul hXM hpow hwn.le (hX.trans hXM)
      _ = 2 ^ n * max c₀ c := mul_comm _ _
  · have hy0 : 0 < y := by linarith
    have hyn : 0 < y ^ n := pow_pos hy0 n
    have hd := hdecay hy0
    rw [Real.rpow_neg hy0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hyn] at hd
    have hw2 : bracketOnePlus y ≤ 2 * y := by
      unfold bracketOnePlus
      linarith
    have hpow : bracketOnePlus y ^ n ≤ 2 ^ n * y ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hw.le hw2 n
    calc X * bracketOnePlus y ^ n ≤ X * (2 ^ n * y ^ n) := mul_le_mul_of_nonneg_left hpow hX
      _ = 2 ^ n * (X * y ^ n) := by ring
      _ ≤ 2 ^ n * max c₀ c :=
        mul_le_mul_of_nonneg_left (hd.trans (le_max_right c₀ c)) h2n.le
end YangMills.Construction.FreeKernel
end
