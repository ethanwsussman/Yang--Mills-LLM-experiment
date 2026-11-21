import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ObjectsOfThePivotCorrection
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def DoubleBlockPathLengths : Prop :=
  ∀ L m K k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K → PathLengthBounds L m K k
end YangMills.Construction.PeriodicLattice
end
