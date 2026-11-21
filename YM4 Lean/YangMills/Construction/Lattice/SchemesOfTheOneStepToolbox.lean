import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
abbrev oneStepAverage (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  schemeBlockAverage s W
def IsOneStepAverageFormed (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Prop :=
  IsSchemeAverageDefined s W c
end PeriodicLattice
end
end YangMills.Construction
