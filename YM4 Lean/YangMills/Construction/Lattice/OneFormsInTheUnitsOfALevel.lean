import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace SeparatedSequences
variable {L m : ℕ} (S : ScaleData)
def levelUnitForm (j : ℕ) (A : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  fun b => ((S.levelMesh L j : ℝ) : ℂ) • A b
def bondFunction (A : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  fun b => ((S.finestMesh L : ℝ) : ℂ) • A b
end SeparatedSequences
end YangMills.Construction
end
