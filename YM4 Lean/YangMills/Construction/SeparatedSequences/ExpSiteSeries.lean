import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def expSiteSeries (L : ℕ) (a : ℝ) : ℝ :=
  9 * (L : ℝ) ^ 4 *
    ∑' r : ℕ+, (2 * ((r : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-a * (((r : ℕ) : ℝ) - 1) / 2)
end YangMills.Construction.SeparatedSequences
end
