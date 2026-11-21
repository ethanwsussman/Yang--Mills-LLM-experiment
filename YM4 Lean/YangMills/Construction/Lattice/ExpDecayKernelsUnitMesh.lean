import YangMills.Construction.Lattice.LocalizedDecayAnyMesh
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
end PeriodicLattice
namespace DirichletLaplacian
open PeriodicLattice
def unitMeshDecayConst (d : ℕ) (θmax : ℝ) : ℝ :=
  8 * (d : ℝ) ^ 4 * 3 ^ d * Real.exp ((2 * (d : ℝ) + 2) * θmax)
end DirichletLaplacian
end YangMills.Construction
