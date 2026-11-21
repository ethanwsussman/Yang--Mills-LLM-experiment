import YangMills.Construction.ClusterExpansionOfAStep.ColumnFloor
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CoreColumns
open TorusLumps
theorem columnFloorExists_holds : ColumnFloorExists := by
  intro c rt L hc hrt hL
  set K : ℝ := (2 / (1 - Real.exp (-(7 * rt / 2 ^ 8)))) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := rt / 2 ^ 6 * 21 with ha
  set b : ℝ := a + 43 with hb
  set U : ℝ := max 1 (max (b / c) ((192 + 8 * K) / c)) with hU
  have hU1 : 1 ≤ U := le_max_left _ _
  refine ⟨max (U ^ (100 : ℕ)) (1 / c), fun x hx => ?_⟩
  have hx1 : U ^ (100 : ℕ) ≤ x := (le_max_left _ _).trans hx
  have hx2 : 1 / c ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx1
  have hcx : 1 ≤ c * x := by
    rw [div_le_iff₀ hc] at hx2
    linarith
  refine ⟨hcx, ?_⟩
  set u : ℝ := x ^ ((1 : ℝ) / 100) with hu
  have hu100 : u ^ (100 : ℕ) = x := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hu0 : 0 < u := Real.rpow_pos_of_pos hxpos _
  have huU : U ≤ u := by
    by_contra hlt
    have h1 : u ^ (100 : ℕ) < U ^ (100 : ℕ) := pow_lt_pow_left₀ (not_le.mp hlt) hu0.le (by norm_num)
    rw [hu100] at h1
    linarith
  have hu1 : 1 ≤ u := hU1.trans huU
  have hub : b ≤ c * u := by
    have : b / c ≤ u := (le_trans (le_max_left _ _) (le_max_right _ _)).trans huU
    rw [div_le_iff₀ hc] at this
    linarith
  have huk : 192 + 8 * K ≤ c * u := by
    have : (192 + 8 * K) / c ≤ u := (le_trans (le_max_right _ _) (le_max_right _ _)).trans huU
    rw [div_le_iff₀ hc] at this
    linarith
  have hu2 : u ^ 2 ≤ x := by
    rw [← hu100]
    exact pow_le_pow_right₀ hu1 (by norm_num)
  have hr : (clusterRange x : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one hu0.le).le
  have hD : (nearGap L (clusterRange x) : ℝ) ≤ 21 * u := by
    have h1 : nearGap L (clusterRange x) ≤ 10 * clusterRange x + 1 := by
      unfold nearGap
      have := Nat.div_le_self (10 * clusterRange x) L
      omega
    have h2 : (nearGap L (clusterRange x) : ℝ) ≤ 10 * (clusterRange x : ℝ) + 1 := by exact_mod_cast h1
    linarith
  set Dn := nearGap L (clusterRange x) with hDn
  have hpow : (2 * (Dn : ℝ) + 1) ^ 4 ≤ 24 * Real.exp (43 * u) := by
    have h1 : 2 * (Dn : ℝ) + 1 ≤ 43 * u := by linarith
    have h2 : (43 * u) ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp (43 * u) :=
      Real.pow_div_factorial_le_exp _ (by positivity) 4
    have h3 : (2 * (Dn : ℝ) + 1) ^ 4 ≤ (43 * u) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
    have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h4, div_le_iff₀ (by norm_num)] at h2
    linarith
  have hexp : Real.exp (rt / 2 ^ 6 * Dn) ≤ Real.exp (a * u) := by
    rw [Real.exp_le_exp, ha]
    have : 0 < rt / 2 ^ 6 := by positivity
    nlinarith
  have hcol : columnConstant rt Dn ≤ 24 * Real.exp (b * u) + K := by
    unfold columnConstant
    have h1 : Real.exp (rt / 2 ^ 6 * Dn) * (2 * (Dn : ℝ) + 1) ^ 4 ≤
        Real.exp (a * u) * (24 * Real.exp (43 * u)) :=
      mul_le_mul hexp hpow (by positivity) (Real.exp_pos _).le
    have h2 : Real.exp (a * u) * (24 * Real.exp (43 * u)) = 24 * Real.exp (b * u) := by
      rw [hb, add_mul, Real.exp_add]
      ring
    linarith
  have hcu2 : c * u ≤ c * u ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    nlinarith
  have hbu : b * u ≤ c * u ^ 2 := by nlinarith
  have hE1 : Real.exp (b * u) ≤ Real.exp (c * x) := by
    rw [Real.exp_le_exp]
    have : c * u ^ 2 ≤ c * x := mul_le_mul_of_nonneg_left hu2 hc.le
    linarith
  have hE2 : 192 + 8 * K ≤ Real.exp (c * x) := by
    have h1 : c * u ≤ c * x := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      nlinarith
    have := Real.add_one_le_exp (c * x)
    linarith
  have hE3 : 1 ≤ Real.exp (b * u) := Real.one_le_exp (by positivity)
  have hsplit : Real.exp (2 * c * x) = Real.exp (c * x) * Real.exp (c * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc 8 * columnConstant rt Dn ≤ 192 * Real.exp (b * u) + 8 * K := by linarith
    _ ≤ (192 + 8 * K) * Real.exp (b * u) := by nlinarith
    _ ≤ Real.exp (c * x) * Real.exp (c * x) :=
        mul_le_mul hE2 hE1 (by positivity) (Real.exp_pos _).le
end YangMills.Construction.CoreColumns
end
