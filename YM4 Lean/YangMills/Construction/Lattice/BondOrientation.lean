import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
namespace Bond
theorem opposite_involutive : Function.Involutive (opposite : Bond L m j → Bond L m j) := fun b => by
  cases b; rfl
end Bond
end YangMills.Construction.PeriodicLattice
