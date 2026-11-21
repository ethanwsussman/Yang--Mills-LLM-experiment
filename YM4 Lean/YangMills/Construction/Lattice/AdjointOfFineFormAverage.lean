import YangMills.Construction.Lattice.AverageTermOnACubeProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace FineFormAverageAdjoint
variable {d N L j : ℕ} (S : Scales d L j N)
include S in
theorem fineScale_pos : 0 < fineScale L j := S.fineMesh.h_pos
end FineFormAverageAdjoint
end YangMills.Construction.PeriodicLattice
