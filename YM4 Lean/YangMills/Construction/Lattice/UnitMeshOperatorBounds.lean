import YangMills.Construction.Lattice.DirichletLaplacianUnitMesh
import YangMills.Construction.Lattice.LocalizedDecayAnyMesh
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.DirichletLaplacian
open PeriodicLattice
def greenDecayRate (d : ℕ) (a : ℝ) : ℝ := 1 / 2 * Real.log (1 + a / (2 * (12 * (d : ℝ) - 8)))
variable {d N : ℕ} {hN : 0 < N}
end YangMills.Construction.DirichletLaplacian
