import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.ChainScales
variable {d : ℕ} {S : ℝ}
structure ScaleFacts (L : ℕ) (ξ : ℝ) (M t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  lastNonemptyIndex_le : lastNonemptyIndex Ω ≤ t
  last_nonempty : (Ω (lastNonemptyIndex Ω)).Nonempty
  eq_empty_of_lt : ∀ n, lastNonemptyIndex Ω < n → Ω n = ∅
  succ_subset : ∀ n, Ω (n + 1) ⊆ Ω n
  side_even_multiple : ∃ u : ℕ, 1 ≤ u ∧ M = L ^ u ∧
    ∀ i : ℤ, i ≤ (lastNonemptyIndex Ω : ℤ) + (u : ℤ) →
      ∃ k : ℕ, 0 < k ∧ S = 2 * (k : ℝ) * scaleSpacing L ξ i
  two_mul_le_side : ∀ n, (Ω n).Nonempty → 2 * (M : ℝ) * scaleSpacing L ξ n ≤ S
def ScalesStatement : Prop :=
  ∀ (d L : ℕ) (S ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), 2 ≤ L →
    IsSeparatedChain L ξ M R₁ t Ω → ScaleFacts L ξ M t Ω
end YangMills.Construction.Torus.ChainScales
end
