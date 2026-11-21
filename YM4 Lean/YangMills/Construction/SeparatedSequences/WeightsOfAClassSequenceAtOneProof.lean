import YangMills.Construction.SeparatedSequences.WeightsOfAClassSequenceAtOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.UnitMassWeights
open SingleSequence
theorem one_sub_pow_succ_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℕ) : 0 < 1 - x ^ (n + 1) := by
  have : x ^ (n + 1) ≤ x := pow_le_of_le_one h0.le h1.le (Nat.succ_ne_zero n)
  linarith
theorem ratio_succ_eq {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℕ) :
    (1 - x) / (1 - x ^ (n + 1 + 1)) =
      ((1 - x) / (1 - x ^ (n + 1))) / (x + (1 - x) / (1 - x ^ (n + 1))) := by
  have hd := one_sub_pow_succ_pos h0 h1 n
  have hs : x + (1 - x) / (1 - x ^ (n + 1)) = (1 - x ^ (n + 1 + 1)) / (1 - x ^ (n + 1)) := by
    rw [eq_div_iff hd.ne', add_mul, div_mul_cancel₀ _ hd.ne']
    ring
  rw [hs, div_div_div_cancel_right₀ hd.ne']
theorem ratio_mem_bounds {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℕ) :
    1 - x ≤ (1 - x) / (1 - x ^ (n + 1)) ∧ (1 - x) / (1 - x ^ (n + 1)) ≤ 1 := by
  have hd := one_sub_pow_succ_pos h0 h1 n
  have hp : 0 < x ^ (n + 1) := pow_pos h0 _
  have hle : x ^ (n + 1) ≤ x := pow_le_of_le_one h0.le h1.le (Nat.succ_ne_zero n)
  constructor
  · rw [le_div_iff₀ hd]
    nlinarith
  · rw [div_le_one hd]
    linarith
variable (s : SequenceData)
theorem inv_sq_pos : 0 < s.Lreal ^ (-2 : ℤ) := by
  have hL : (0 : ℝ) < s.Lreal := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : 0 < s.data.L)
  exact zpow_pos hL _
theorem inv_sq_lt_one : s.Lreal ^ (-2 : ℤ) < 1 := by
  have hL : (1 : ℝ) < s.Lreal := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : 1 < s.data.L)
  exact zpow_lt_one_of_neg₀ hL (by norm_num)
theorem levelWeight_succ (n : ℕ) :
    s.params.levelWeight (n + 1) =
      (1 - s.Lreal ^ (-2 : ℤ)) / (1 - (s.Lreal ^ (-2 : ℤ)) ^ (n + 1)) := by
  have hp : s.Lreal ^ (-(2 * ((n + 1 : ℕ) : ℤ))) = (s.Lreal ^ (-2 : ℤ)) ^ (n + 1) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
  rw [← hp]
  show (1 : ℝ) * (1 - s.Lreal ^ (-2 : ℤ)) / (1 - s.Lreal ^ (-(2 * ((n + 1 : ℕ) : ℤ)))) = _
  rw [one_mul]
theorem proof : UnitMassWeightsStatement := by
  intro s
  have h0 := inv_sq_pos s
  have h1 := inv_sq_lt_one s
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [levelWeight_succ]
    congr 2
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
  · rw [show (1 : ℕ) = 0 + 1 from rfl, levelWeight_succ, pow_one]
    exact div_self (by linarith)
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [levelWeight_succ, levelWeight_succ]
    exact ratio_succ_eq h0 h1 k
  · intro n
    cases n with
    | zero =>
      have hw : s.params.levelWeight 0 = 1 := rfl
      rw [hw]
      constructor <;> linarith
    | succ k =>
      rw [levelWeight_succ]
      exact ratio_mem_bounds h0 h1 k
end YangMills.Construction.SeparatedClasses.UnitMassWeights
