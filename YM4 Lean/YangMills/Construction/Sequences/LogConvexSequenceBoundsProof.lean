import YangMills.Construction.Sequences.LogConvexSequenceBounds
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LogConvexSequence
theorem ratioAndPowerBounds_holds : RatioAndPowerBounds := by
  intro x hx hc
  have h1 : ∀ n, x 1 * x n ≤ x 0 * x (n + 1) := by
    intro n
    induction n with
    | zero => simp [mul_comm]
    | succ n ih =>
      rcases (hx (n + 1)).eq_or_lt with h0 | hpos
      · rw [← h0]
        simpa using mul_nonneg (hx 0) (hx (n + 1 + 1))
      · have hcn := hc (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        simp only [Nat.add_sub_cancel] at hcn
        have key : x (n + 1) * (x 1 * x (n + 1)) ≤ x (n + 1) * (x 0 * x (n + 1 + 1)) := by
          calc x (n + 1) * (x 1 * x (n + 1)) = x 1 * x (n + 1) ^ 2 := by ring
            _ ≤ x 1 * (x n * x (n + 1 + 1)) := mul_le_mul_of_nonneg_left hcn (hx 1)
            _ = (x 1 * x n) * x (n + 1 + 1) := by ring
            _ ≤ (x 0 * x (n + 1)) * x (n + 1 + 1) := mul_le_mul_of_nonneg_right ih (hx _)
            _ = x (n + 1) * (x 0 * x (n + 1 + 1)) := by ring
        exact le_of_mul_le_mul_left key hpos
  refine ⟨h1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    calc x 1 ^ (m + 1 + 1) = x 1 * x 1 ^ (m + 1) := by ring
      _ ≤ x 1 * (x 0 ^ m * x (m + 1)) := mul_le_mul_of_nonneg_left ih (hx 1)
      _ = x 0 ^ m * (x 1 * x (m + 1)) := by ring
      _ ≤ x 0 ^ m * (x 0 * x (m + 1 + 1)) :=
        mul_le_mul_of_nonneg_left (h1 _) (pow_nonneg (hx 0) _)
      _ = x 0 ^ (m + 1) * x (m + 1 + 1) := by ring
end YangMills.Construction.LogConvexSequence
