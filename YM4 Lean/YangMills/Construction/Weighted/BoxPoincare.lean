import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def integerBox (M : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
def BoxPoincareInequality : Prop :=
  ∀ (M : ℕ) (g : (Fin 4 → ℤ) → ℝ) (m : ℝ),
    m = ((2 * (M : ℝ) + 1) ^ 4)⁻¹ * ∑ k ∈ integerBox M, g k →
      ∑ k ∈ integerBox M, (g k - m) ^ 2 ≤
        (2 * (M : ℝ) + 1) ^ 2 * ∑ μ : Fin 4,
          ∑ k ∈ (integerBox M).filter (fun k => k + Pi.single μ 1 ∈ integerBox M),
            (g (k + Pi.single μ 1) - g k) ^ 2
end YangMills.Construction.Weighted
