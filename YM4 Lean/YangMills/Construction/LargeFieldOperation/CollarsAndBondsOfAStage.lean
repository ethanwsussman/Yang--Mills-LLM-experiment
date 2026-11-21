import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def bondsMeetingAvoiding (j : ℕ) (A B : Set (FourTorus L m)) : Set (BondAtLevel L m K j) :=
  {b | ((b.source : FourTorus L m) ∈ A ∨ (b.target : FourTorus L m) ∈ A) ∧
    (b.source : FourTorus L m) ∉ B ∧ (b.target : FourTorus L m) ∉ B}
end YangMills.Construction.PeriodicLattice
