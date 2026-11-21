import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Lattice
def siteNearnessRadius (L : ℕ) : ℝ :=
  4 * (L : ℝ) + 8
end YangMills.Construction.Lattice
