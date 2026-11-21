import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences
variable {L m : ℕ} (S : ScaleData)
def positiveBondsInside (X : Set (FourTorus L m)) : Set (FineBond L m S) :=
  {b | b ∈ (bondsInside X : Set (FineBond L m S)) ∧ b.IsPositivelyOriented}
end YangMills.Construction.SeparatedSequences
