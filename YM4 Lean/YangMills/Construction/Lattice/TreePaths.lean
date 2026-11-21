import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def lastLinkOfPath (y' : GridPoint d S.coarseMesh) (y : GridPoint d S.unitMesh)
    (h : y ≠ S.coarseToUnit y') : Link d S.unitMesh :=
  (firstDifferingAxis (S.coarseToUnit y') y h,
    y - S.unitMesh.basisStep (firstDifferingAxis (S.coarseToUnit y') y h))
end Scales
end YangMills.Construction.PeriodicLattice
