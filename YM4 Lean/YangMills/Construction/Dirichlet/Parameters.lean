import Mathlib
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Dirichlet
structure Parameters (d L : ℕ) (lower upper : ℝ) : Prop where
  three_le_dim : 3 ≤ d
  three_le_blockFactor : 3 ≤ L
  odd_blockFactor : Odd L
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
structure IsEvenBump (f : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ f
  even : ∀ x, f (-x) = f x
  nonneg : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  eq_one_of_mem : ∀ x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), f x = 1
  eq_zero_of_not_mem : ∀ x, x ∉ Set.Icc (-(2 / 3) : ℝ) (2 / 3) → f x = 0
theorem exists_isEvenBump : ∃ f : ℝ → ℝ, IsEvenBump f := by
  refine ⟨fun x => Real.smoothTransition ((4 / 9 - x ^ 2) * (36 / 7)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · intro x
    simp
  · intro x
    exact Real.smoothTransition.nonneg _
  · intro x
    exact Real.smoothTransition.le_one _
  · rintro x ⟨h₁, h₂⟩
    apply Real.smoothTransition.one_of_one_le
    nlinarith
  · intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have h : x < -(2 / 3) ∨ 2 / 3 < x := by
      by_contra hc
      exact hx ⟨not_lt.mp fun h => hc (Or.inl h), not_lt.mp fun h => hc (Or.inr h)⟩
    rcases h with h | h <;> nlinarith
def bumpProfile : ℝ → ℝ := Classical.choose exists_isEvenBump
theorem bumpProfile_isEvenBump : IsEvenBump bumpProfile :=
  Classical.choose_spec exists_isEvenBump
end YangMills.Construction.Dirichlet
