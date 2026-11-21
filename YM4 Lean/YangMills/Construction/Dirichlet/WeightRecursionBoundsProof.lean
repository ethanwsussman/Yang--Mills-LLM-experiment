import YangMills.Construction.Dirichlet.WeightRecursionBounds
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Dirichlet
theorem weightRecursionBounds_holds : WeightRecursionBounds := by
  intro L hL _ a ha0 ha1 hstep
  have hLr : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hpow : ∀ n : ℕ, (L : ℝ) ^ (-(2 * (n : ℤ))) = ((L : ℝ) ^ (-2 : ℤ)) ^ n := by
    intro n
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
  have hx0 : 0 < (L : ℝ) ^ (-2 : ℤ) := zpow_pos hLpos _
  have hx1 : (L : ℝ) ^ (-2 : ℤ) < 1 := by
    have h : (L : ℝ) ^ (-2 : ℤ) = ((L : ℝ) ^ 2)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [h]
    apply inv_lt_one_of_one_lt₀
    nlinarith
  simp only [hpow]
  generalize (L : ℝ) ^ (-2 : ℤ) = x at hx0 hx1 hstep ⊢
  have hlt : ∀ n : ℕ, 1 ≤ n → 0 < 1 - x ^ n := by
    intro n hn
    have : x ^ n < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
    linarith
  have hclosed : ∀ n : ℕ, 1 ≤ n → a n = (1 - x) / (1 - x ^ n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have : 1 - x ≠ 0 := by linarith
      rw [ha1, pow_one, div_self this]
    | succ n hn ih =>
      have hd := hlt n hn
      have hd1 := hlt (n + 1) (by omega)
      have hsum : x + (1 - x) / (1 - x ^ n) = (1 - x ^ (n + 1)) / (1 - x ^ n) := by
        field_simp
        ring
      rw [hstep n hn, ih, hsum]
      field_simp
  refine ⟨hclosed, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ha0]
    constructor <;> linarith
  · have hd := hlt n hn
    have hxn : 0 < x ^ n := pow_pos hx0 n
    have hxle : x ^ n ≤ x := pow_le_of_le_one hx0.le hx1.le (by omega)
    rw [hclosed n hn]
    constructor
    · rw [lt_div_iff₀ hd]
      nlinarith
    · rw [div_le_one hd]
      linarith
end YangMills.Construction.Dirichlet
