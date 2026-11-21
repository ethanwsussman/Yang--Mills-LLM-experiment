import Mathlib
open Filter
namespace YangMills.ReferenceCalibration

/-- Choose a stopping level on a torus whose physical side is fixed. The number
of remaining lattice units is comparable to a small power of the inverse
coupling, unless the bare lattice already lies on the smaller side. -/
theorem exists_reference_stopping_scale
    {L K : ℕ} {x : ℕ → ℝ} {B : ℝ} (htop : 1 ≤ x K)
    (hstep : ∀ j < K, x (j + 1) ≤ x j + B) :
    ∃ k ≤ K, let n := (L : ℝ) ^ (K - k)
      n ^ 92 ≤ x k ∧ (k = 0 ∨ x k < ((L : ℝ) * n) ^ 92 + B) := by
  classical
  let ok (i : ℕ) := i ≤ K ∧ ((L : ℝ) ^ (K - i)) ^ 92 ≤ x i
  have hex : ∃ i, ok i := ⟨K, le_rfl, by simpa using htop⟩
  let k := Nat.find hex
  obtain ⟨hk, hx⟩ := Nat.find_spec hex
  refine ⟨k, hk, hx, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exact Or.inl h0
  · right
    have hprev := Nat.find_min hex (show k - 1 < k by omega)
    have hfail : x (k - 1) < ((L : ℝ) ^ (K - (k - 1))) ^ 92 :=
      lt_of_not_ge fun h => hprev ⟨by omega, h⟩
    have hinc := hstep (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hinc
    rw [show K - (k - 1) = K - k + 1 by omega, pow_succ' (L : ℝ) (K - k)] at hfail
    linarith

end YangMills.ReferenceCalibration
