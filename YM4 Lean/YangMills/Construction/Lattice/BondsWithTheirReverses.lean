import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
section Orientation
variable (hO : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hO in
theorem not_isPositivelyOriented_opposite {b : Bond L m j} (hp : b.IsPositivelyOriented) :
    ¬b.opposite.IsPositivelyOriented := by
  rcases hO b with h | h
  · exact h.2
  · exact absurd hp h.2
include hO in
theorem isPositivelyOriented_opposite {b : Bond L m j} (hp : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  rcases hO b with h | h
  · exact absurd h.1 hp
  · exact h.1
end Orientation
end YangMills.Construction.PeriodicLattice
end
