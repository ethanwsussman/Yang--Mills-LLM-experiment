import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
variable {L m K k : ℕ}
def blockFieldLift (j : ℕ) (V : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K j → ComplexMatrix2 :=
  blockFieldAtLevel (Averaging.smoothingRadius L) j (bareLiftFromLevel (K := K) V)
end PeriodicLattice
end YangMills.Construction
