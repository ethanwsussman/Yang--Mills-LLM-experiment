import YangMills.Construction.Dirichlet.BlockGapFloors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Dirichlet.FloorComparison
def comparisonRate (d : ℕ) (L : ℝ) : ℝ :=
  (1 - (L ^ 2)⁻¹) / (8 * (d : ℝ) * (L ^ 2 + 1))
def FloorComparisonStatement : Prop :=
  ∀ (d : ℕ) (L δ m r : ℝ), d = 4 → L ≥ 13 →
    0 < δ → δ ≤ 1 / 4 * comparisonRate d L → m ≥ L ^ 2 →
    r ≥ 4 * ((d : ℝ) + 2) * Real.log L / δ →
    m ≥ L + 10 ∧
      r ≥ max (L * (L + 9)) (((d : ℝ) + 2) * (comparisonRate d L)⁻¹ * Real.log L) ∧
      ∀ M R₁ : ℝ, M ≥ m → R₁ * M ≥ r →
        YangMills.Construction.Dirichlet.FloorsAtRate d L (comparisonRate d L) M R₁
end YangMills.Construction.Dirichlet.FloorComparison
