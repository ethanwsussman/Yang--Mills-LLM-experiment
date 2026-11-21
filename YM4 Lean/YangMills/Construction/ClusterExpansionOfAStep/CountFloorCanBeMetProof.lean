import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
theorem couplingFloorExists_holds : CouplingFloorExists := by
  intro c L rt hc
  set K : ℝ := |2 ^ 16 + 2 ^ 7 * rt| + 1 with hK
  have hK1 : 1 ≤ K := by
    have := abs_nonneg (2 ^ 16 + 2 ^ 7 * rt : ℝ)
    linarith
  set m : ℝ := 16 * K / c with hm
  refine ⟨max (max 1 ((L : ℝ) ^ 100)) (m ^ 2), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxL : (L : ℝ) ^ 100 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxm : m ^ 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  set s : ℝ := x ^ ((1 : ℝ) / 100) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hx1 (by norm_num)
  have hs0 : 0 ≤ s := by linarith
  have hs100 : s ^ 100 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hrs : (clusterRange x : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hsr : s ≤ (clusterRange x : ℝ) := Nat.le_ceil s
  constructor
  · have hLs : (L : ℝ) ≤ s := by
      refine le_of_pow_le_pow_left₀ (n := 100) (by norm_num) hs0 ?_
      rw [hs100]
      exact hxL
    exact_mod_cast hLs.trans hsr
  · have hr0 : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
    have hr4 : (clusterRange x : ℝ) ^ 4 ≤ 16 * s ^ 4 := by
      calc (clusterRange x : ℝ) ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ hr0 (by linarith) _
        _ = 16 * s ^ 4 := by ring
    have hs96 : m ≤ s ^ 96 := by
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
      calc m ^ 2 ≤ x := hxm
        _ = s ^ 100 := hs100.symm
        _ ≤ s ^ 192 := pow_le_pow_right₀ hs1 (by norm_num)
        _ = (s ^ 96) ^ 2 := by ring
    have hs4 : 0 ≤ s ^ 4 := by positivity
    calc (2 ^ 16 + 2 ^ 7 * rt) * (clusterRange x : ℝ) ^ 4 ≤ K * (clusterRange x : ℝ) ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := le_abs_self (2 ^ 16 + 2 ^ 7 * rt : ℝ)
          linarith
      _ ≤ K * (16 * s ^ 4) := mul_le_mul_of_nonneg_left hr4 (by linarith)
      _ = c * (m * s ^ 4) := by
          rw [hm]
          field_simp
      _ ≤ c * (s ^ 96 * s ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hc.le
          exact mul_le_mul_of_nonneg_right hs96 hs4
      _ = c * x := by
          rw [← hs100]
          ring
end YangMills.Construction.TorusLumps
end
