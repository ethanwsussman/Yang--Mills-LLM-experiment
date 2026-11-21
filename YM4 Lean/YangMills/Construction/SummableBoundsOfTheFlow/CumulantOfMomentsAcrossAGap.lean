import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Cumulants
noncomputable def partitionWeightSum (p : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin p)),
    ((π.parts.card - 1).factorial : ℝ) * (π.parts.card : ℝ)
def CumulantSmallAcrossGap : Prop :=
  ∀ (p : ℕ) (S : Finset (Fin p)) (μ : Finset (Fin p) → ℝ) (w : Fin p → ℝ) (ε : ℝ),
    S.Nonempty → Sᶜ.Nonempty → μ ∅ = 1 → (∀ k, 0 ≤ w k) → 0 ≤ ε →
    (∀ U, |μ U| ≤ ∏ k ∈ U, w k) →
    (∀ B, |μ B - μ (B ∩ S) * μ (B \ S)| ≤ ε * ∏ k ∈ B, w k) →
    |∑ π : Finpartition (Finset.univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, μ B| ≤
      partitionWeightSum p * ε * ∏ k, w k
end YangMills.Construction.Cumulants
