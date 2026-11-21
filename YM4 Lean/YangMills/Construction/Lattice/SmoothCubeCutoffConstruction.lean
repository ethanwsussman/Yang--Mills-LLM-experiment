import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeCutoff
def posPartSq (r : ℝ) : ℝ := (max r 0) ^ 2
def plateauProfile (s : ℝ) : ℝ :=
  1 - 2 * posPartSq (s - 2) + 4 * posPartSq (s - 5 / 2) - 2 * posPartSq (s - 3)
variable {d N : ℕ}
def circleBump (t : AddCircle (N : ℝ)) : ℝ := plateauProfile ‖t‖
end YangMills.Construction.PeriodicLattice.CubeCutoff
