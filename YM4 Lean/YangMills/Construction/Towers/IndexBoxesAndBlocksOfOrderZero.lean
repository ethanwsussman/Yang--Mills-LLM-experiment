import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def offsetBox (L n : ℕ) : Set (Fin 4 → ℤ) :=
  {ν | ∀ μ, |(ν μ : ℝ)| ≤ ((L : ℝ) ^ n - 1) / 2}
theorem mem_offsetBox_iff {L n : ℕ} {ν : Fin 4 → ℤ} :
    ν ∈ offsetBox L n ↔ ∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ n - 1 := by
  refine forall_congr' fun μ => ?_
  rw [← Int.cast_le (R := ℝ)]
  push_cast
  constructor <;> intro h <;> linarith
end YangMills.Construction.Tower
end
