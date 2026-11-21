import YangMills.Construction.ResponseInTheExpansion.WeightAgainstAnExponential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open BlockAverages
theorem decayFactorExpBound_holds : DecayFactorExpBound := by
  intro L δ hL hδ
  set n₁ : ℝ := (L : ℝ) ^ (1 / 640 : ℝ) with hn₁
  have hn : 0 < n₁ := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  set C : ℝ := 1 + (Nat.factorial 16000 : ℝ) / (δ * n₁) ^ 16000 with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ (Nat.factorial 16000 : ℝ) / (δ * n₁) ^ 16000 := by positivity
    linarith
  refine ⟨C, hC1, fun u hu => ?_⟩
  unfold torusDecayFactor
  have h1 : max 1 ((u / n₁) ^ 16000) ≤ C * Real.exp (δ * u) := by
    have hexp : 1 ≤ Real.exp (δ * u) := Real.one_le_exp (by positivity)
    refine max_le ?_ ?_
    · nlinarith
    · have h2 := Real.pow_div_factorial_le_exp (δ * u) (by positivity) 16000
      have e : (u / n₁) ^ 16000 = (Nat.factorial 16000 : ℝ) / (δ * n₁) ^ 16000 *
          ((δ * u) ^ 16000 / (Nat.factorial 16000 : ℝ)) := by
        have hf : (Nat.factorial 16000 : ℝ) ≠ 0 := by positivity
        rw [div_pow, mul_pow, mul_pow]
        field_simp
      rw [e]
      have h3 : 0 ≤ (Nat.factorial 16000 : ℝ) / (δ * n₁) ^ 16000 := by positivity
      calc _ ≤ (Nat.factorial 16000 : ℝ) / (δ * n₁) ^ 16000 * Real.exp (δ * u) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ ≤ C * Real.exp (δ * u) := by
            have := Real.exp_pos (δ * u)
            rw [hC]
            nlinarith
  calc max 1 ((u / n₁) ^ 16000) * Real.exp (δ * u) ≤ C * Real.exp (δ * u) * Real.exp (δ * u) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = C * Real.exp (2 * δ * u) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
end YangMills.Construction.LinearResponse
end
