import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def bondAxisFunctionSpace (Y : Set (FourTorus L m)) : Set (FineBond L m S × Fin 4 → ComplexMatrix2) :=
  {X | (∀ i, X i ∈ complexLieAlgebra) ∧ ∀ i ∉ bondAxisIndexSet S Y, X i = 0}
end YangMills.Construction.SequenceTriples
end
