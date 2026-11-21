import YangMills.Construction.LawInAState.SizeOfTheBoundOfOneTrace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
theorem pairTraceBoundIsSmall_holds : PairTraceBoundIsSmall := by
  intro c₄ M C₁ c₁ vt hc₄ hM hC₁ hc₁ hvt
  set A₀ : ℝ := C₁ / vt + C₁ * (24 / c₁ ^ 4) + M with hA₀
  refine ⟨15 ^ 8 * (c₄ * (576 + 2 * c₄) * M ^ 2) + 15 ^ 8 * (6 ^ 4 * 288 ^ 2) * (A₀ * (3 * M + 6 * C₁)), by positivity, ?_⟩
  intro n R err hn hnR herr hv hle
  have hn0 : 0 < n := by linarith
  have hR0 : 0 < R := by linarith
  set q : ℝ := n⁻¹ + n ^ 4 * (R ^ 4)⁻¹ with hq
  have hninv : n⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hRinv : n ^ 4 * (R ^ 4)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hn0.le hnR 4
  have hq2 : q ≤ 2 := by linarith
  have hexp : Real.exp (-(c₁ * R)) ≤ 24 / c₁ ^ 4 * (R ^ 4)⁻¹ := by
    have h1 := Real.pow_div_factorial_le_exp (c₁ * R) (by positivity) 4
    have h2 : (0 : ℝ) < (c₁ * R) ^ 4 / (Nat.factorial 4 : ℝ) := by positivity
    rw [Real.exp_neg]
    calc (Real.exp (c₁ * R))⁻¹ ≤ ((c₁ * R) ^ 4 / (Nat.factorial 4 : ℝ))⁻¹ := inv_anti₀ h2 h1
      _ = _ := by
        simp only [Nat.factorial]
        push_cast
        field_simp
  have hexp1 : Real.exp (-(c₁ * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 < c₁ * R := by positivity
    linarith)
  have hR4 : (R ^ 4)⁻¹ ≤ q := by
    have h1 : (R ^ 4)⁻¹ ≤ n ^ 4 * (R ^ 4)⁻¹ := by
      have : 1 ≤ n ^ 4 := one_le_pow₀ hn
      have h2 : 0 ≤ (R ^ 4)⁻¹ := by positivity
      nlinarith
    have : 0 ≤ n⁻¹ := by positivity
    linarith
  have hR5 : (R ^ 5)⁻¹ ≤ (R ^ 4)⁻¹ := by
    have h1 : 1 ≤ R := hn.trans hnR
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by norm_num))
  have hnq : n⁻¹ ≤ q := by
    have : 0 ≤ n ^ 4 * (R ^ 4)⁻¹ := by positivity
    linarith
  have hvq : (vt * n)⁻¹ ≤ q / vt := by
    rw [mul_inv, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right hnq (by positivity)
  have herr2 : err ≤ 2 * C₁ := by
    have : C₁ * ((vt * n)⁻¹ + Real.exp (-(c₁ * R))) ≤ C₁ * 2 := mul_le_mul_of_nonneg_left (by linarith) hC₁
    linarith
  set e₁ : ℝ := err + M * (R ^ 5)⁻¹ with he₁
  have hMR : M * (R ^ 5)⁻¹ ≤ M * q := mul_le_mul_of_nonneg_left (hR5.trans hR4) hM
  have he₁q : e₁ ≤ A₀ * q := by
    have h1 : err ≤ C₁ * (q / vt + 24 / c₁ ^ 4 * q) := by
      refine hle.trans (mul_le_mul_of_nonneg_left (add_le_add hvq ?_) hC₁)
      exact hexp.trans (mul_le_mul_of_nonneg_left hR4 (by positivity))
    have e2 : A₀ * q = C₁ * (q / vt + 24 / c₁ ^ 4 * q) + M * q := by
      rw [hA₀]; ring
    rw [he₁, e2]
    linarith
  have hR5' : (R ^ 5)⁻¹ ≤ 1 := by
    have h1 : 1 ≤ R := hn.trans hnR
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hMR1 : M * (R ^ 5)⁻¹ ≤ M := by nlinarith
  have he₁b : e₁ ≤ 2 * C₁ + M := by rw [he₁]; linarith
  have hsum : 2 * (M + err) + e₁ ≤ 3 * M + 6 * C₁ := by linarith
  have hE : n ^ 4 * ((n ^ 5)⁻¹ + (R ^ 4)⁻¹) = q := by
    rw [hq]; field_simp
  have e1 : (15 * n) ^ 8 * ((c₄ * ((n ^ 5)⁻¹ + (R ^ 4)⁻¹)) * (2 * (288 * (n ^ 4)⁻¹) + c₄ * ((n ^ 5)⁻¹ + (R ^ 4)⁻¹)) * M ^ 2) =
      15 ^ 8 * (c₄ * q * (576 + c₄ * q) * M ^ 2) := by
    rw [← hE]
    field_simp
    ring
  have e2 : (15 * n) ^ 8 * (6 ^ 4 * (e₁ * (2 * (M + err) + e₁) * (288 * (n ^ 4)⁻¹) ^ 2)) =
      15 ^ 8 * (6 ^ 4 * 288 ^ 2) * (e₁ * (2 * (M + err) + e₁)) := by
    field_simp
  have b1 : c₄ * q * (576 + c₄ * q) * M ^ 2 ≤ c₄ * (576 + 2 * c₄) * M ^ 2 * q := by
    have h0 : c₄ * q ≤ c₄ * 2 := mul_le_mul_of_nonneg_left hq2 hc₄
    have h1 : 576 + c₄ * q ≤ 576 + 2 * c₄ := by linarith
    have h2 : 0 ≤ c₄ * q * M ^ 2 := by positivity
    calc c₄ * q * (576 + c₄ * q) * M ^ 2 = c₄ * q * M ^ 2 * (576 + c₄ * q) := by ring
      _ ≤ c₄ * q * M ^ 2 * (576 + 2 * c₄) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have b2 : e₁ * (2 * (M + err) + e₁) ≤ A₀ * q * (3 * M + 6 * C₁) :=
    mul_le_mul he₁q hsum (by positivity) (by positivity)
  unfold pairTraceBound
  rw [mul_add, e1, ← he₁, e2]
  calc _ ≤ 15 ^ 8 * (c₄ * (576 + 2 * c₄) * M ^ 2 * q) + 15 ^ 8 * (6 ^ 4 * 288 ^ 2) * (A₀ * q * (3 * M + 6 * C₁)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left b1 (by positivity)) (mul_le_mul_of_nonneg_left b2 (by positivity))
    _ = _ := by ring
end YangMills.Construction.TraceBounds
end
