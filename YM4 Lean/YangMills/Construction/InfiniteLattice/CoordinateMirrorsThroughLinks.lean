import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def halfIntegerLevels (a : ℝ) : Set ℝ := {c | ∃ k : ℤ, c = ((k : ℝ) + 1 / 2) * a}
end InfiniteLattice
end YangMills.Construction
