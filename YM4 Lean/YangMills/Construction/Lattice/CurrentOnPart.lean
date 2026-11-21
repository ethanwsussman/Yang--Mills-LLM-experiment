import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ} {j : ℤ}
def Plaquette.HasBond (p : Plaquette L m j) (b : Bond L m j) : Prop :=
  b ∈ p.boundaryBonds ∨ b.opposite ∈ p.boundaryBonds
def plaquettesThrough (b : Bond L m j) : Set (Plaquette L m j) :=
  {p | p.HasBond b}
def Plaquette.BondsWithin (p : Plaquette L m j) (B : Set (Bond L m j)) : Prop :=
  ∀ b ∈ p.boundaryBonds, b ∈ B
end PeriodicLattice
end YangMills.Construction
end
