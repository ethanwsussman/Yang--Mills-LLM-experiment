import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Cumulants
def CumulantShiftInvariant : Prop :=
  ∀ (p : ℕ) (i : Fin p) (μ ν : Finset (Fin p) → ℝ) (c : ℝ), 2 ≤ p → ν ∅ = 1 →
    (∀ B, i ∉ B → μ B = ν B) → (∀ B, i ∈ B → μ B = ν B + c * ν (B.erase i)) →
    ∑ π : Finpartition (Finset.univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, μ B =
    ∑ π : Finpartition (Finset.univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, ν B
end YangMills.Construction.Cumulants
