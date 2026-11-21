import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ScaleLabel
variable {L m K k' k : ℕ} {c : ℕ → ℕ}
def stagedDomain (r : ℕ) (x : ℕ → ℝ) (S : PeriodicLattice.ScaleLabel L m K k' c k)
    (Q : Set (Set (PeriodicLattice.FourTorus L m))) (n i : ℕ) : Set (PeriodicLattice.FourTorus L m) :=
  open Classical in
  if PeriodicLattice.lowerLevel L r x k < (i : ℤ) ∧ (i : ℤ) ≤ PeriodicLattice.lowerLevel L r x k + n then
    S.trimmedDomain r x Q i
  else S.domainSeq i
end YangMills.Construction.PeriodicLattice.ScaleLabel
end
