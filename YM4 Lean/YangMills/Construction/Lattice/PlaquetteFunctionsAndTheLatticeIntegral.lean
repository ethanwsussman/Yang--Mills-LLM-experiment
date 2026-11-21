import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsBoundedPlaquetteFunction (φ : Plaquette L m j → ℝ) : Prop := ∃ C : ℝ, ∀ p, |φ p| ≤ C
end YangMills.Construction.PeriodicLattice
