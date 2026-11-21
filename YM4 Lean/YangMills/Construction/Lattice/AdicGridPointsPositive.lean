import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def adicGridPointsPositive (L : ℕ) : Set ℝ :=
  ⋃ k : ℕ+, {x | ∃ n : ℤ, x = (n : ℝ) * meshSize L ((k : ℕ) : ℤ)}
theorem mem_adicGridPointsPositive_iff (L : ℕ) (x : ℝ) :
    x ∈ adicGridPointsPositive L ↔
      ∃ k : ℕ+, ∃ n : ℤ, x = (n : ℝ) * meshSize L ((k : ℕ) : ℤ) := by
  simp [adicGridPointsPositive]
end PeriodicLattice
end YangMills.Construction
