import YangMills.Construction.SummableBoundsOfTheFlow.AllowanceOfARecursionProof
import YangMills.Construction.SummableBoundsOfTheFlow.LineUpToTheNextLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open Finset
namespace YangMills.Construction.CouplingFlow
variable {b d x : ℕ → ℝ}
theorem sub_eq_sum_Ico_steps (i j : ℕ) (hij : i ≤ j) :
    x i - x j = ∑ l ∈ Ico i j, (b l + (d l / x l - stepRemainder b d x l)) := by apply _root_.YangMills.Construction.CouplingFlow.RecursionBounds.sub_eq_sum_steps <;> assumption
theorem twoSidedDropToNextLevel_holds : TwoSidedDropToNextLevel := by
  intro b d c₀ c M R hc hM hR hd hs
  refine ⟨1 + 4 * (M + R) / c₀, fun X hX x i j hij hx hf => ?_⟩
  have hq : 0 ≤ 4 * (M + R) / c₀ := by positivity
  have hX1 : 1 ≤ X := by linarith
  have hsum := sub_eq_sum_Ico_steps (b := b) (d := d) (x := x) i j hij
  rw [sum_add_distrib] at hsum
  have hsl := abs_le.1 (hs i j hij)
  have hsm : ∀ l ∈ Ico i j, |d l / x l - stepRemainder b d x l| ≤ c₀ / 4 := by
    intro l hl
    have hlt : l < j := (mem_Ico.1 hl).2
    have hXl := hx l hlt
    have hv1 : 1 ≤ x l := hX1.trans hXl
    have hv0 : 0 < x l := by linarith
    have h1 : |d l / x l| ≤ M * (x l)⁻¹ := by
      rw [abs_div, abs_of_pos hv0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hd l) (by positivity)
    have h2 : x l ^ (-(5 / 4) : ℝ) ≤ (x l)⁻¹ := by
      rw [← Real.rpow_neg_one (x l)]
      exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
    have h3 : R * x l ^ (-(5 / 4) : ℝ) ≤ R * (x l)⁻¹ := mul_le_mul_of_nonneg_left h2 hR
    have h4 : (M + R) * (x l)⁻¹ ≤ c₀ / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hv0]
      have h5 : 4 * (M + R) / c₀ ≤ x l := by linarith
      rw [div_le_iff₀ hc] at h5
      linarith
    calc |d l / x l - stepRemainder b d x l| ≤ |d l / x l| + |stepRemainder b d x l| := abs_sub _ _
      _ ≤ M * (x l)⁻¹ + R * (x l)⁻¹ := add_le_add h1 ((hf l hlt).trans h3)
      _ = (M + R) * (x l)⁻¹ := by ring
      _ ≤ c₀ / 4 := h4
  have hcard : ((Ico i j).card : ℝ) = (j : ℝ) - i := by
    rw [Nat.card_Ico, Nat.cast_sub hij]
  have hab : |∑ l ∈ Ico i j, (d l / x l - stepRemainder b d x l)| ≤ ((j : ℝ) - i) * (c₀ / 4) := by
    calc _ ≤ ∑ l ∈ Ico i j, |d l / x l - stepRemainder b d x l| := abs_sum_le_sum_abs _ _
      _ ≤ (Ico i j).card • (c₀ / 4) := sum_le_card_nsmul _ _ _ hsm
      _ = ((j : ℝ) - i) * (c₀ / 4) := by rw [nsmul_eq_mul, hcard]
  have hab' := abs_le.1 hab
  constructor <;> nlinarith [hsl.1, hsl.2, hab'.1, hab'.2]
end YangMills.Construction.CouplingFlow
end
