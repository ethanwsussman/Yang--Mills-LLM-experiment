import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def adicGridPoints (L : ℕ) : Set ℝ :=
  ⋃ k : ℕ, {x | ∃ n : ℤ, x = (n : ℝ) * meshSize L (k : ℤ)}
theorem mem_adicGridPoints_iff (L : ℕ) (x : ℝ) :
    x ∈ adicGridPoints L ↔ ∃ k : ℕ, ∃ n : ℤ, x = (n : ℝ) * meshSize L (k : ℤ) := by
  simp [adicGridPoints]
end YangMills.Construction.PeriodicLattice
