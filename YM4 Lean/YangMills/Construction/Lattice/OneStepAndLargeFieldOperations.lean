import YangMills.Construction.Lattice.FluctuationFormOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
variable {m K : ℕ} (c : ChoiceUpToRadii)
def stepBasePoints (j : ℕ) (D : StepData c.L m K j) : BondAtLevel c.L m K j → Matrices.ComplexMatrix2 :=
  basePoint c.toChoiceUpToDegreeConstants D
end PeriodicLattice.CubesOfStep
end YangMills.Construction
end
