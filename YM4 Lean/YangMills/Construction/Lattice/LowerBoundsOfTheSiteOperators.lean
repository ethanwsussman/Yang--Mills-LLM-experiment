import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators SeparatedSequences
namespace SiteOperatorBounds
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
def blockSpectralGap (n : ℕ) : ℝ :=
  4 * (D.L : ℝ) ^ (2 * n) * Real.sin (Real.pi / (2 * (D.L : ℝ) ^ n)) ^ 2
end SiteOperatorBounds
end YangMills.Construction
end
