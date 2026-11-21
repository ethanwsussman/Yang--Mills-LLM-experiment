import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions SequenceTriples Matrices
open scoped ENNReal
noncomputable section
namespace CommutatorSettings
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def reducedSourceInjOne (A : FineBond L m S → ComplexMatrix2) : ReducedSourceTuple L m S :=
  (reducedInjOne S A, 0)
end CommutatorSettings
end
end YangMills.Construction
