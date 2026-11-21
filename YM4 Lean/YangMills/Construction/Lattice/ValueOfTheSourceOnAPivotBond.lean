import YangMills.Construction.Lattice.NumbersAndFunctionsOfThePivotBond
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K n : ℕ}
def IsPivotEquationSolution (c : BondAtLevel L m K (n + 1)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (a' : LieBondField (setWithoutPivot c)) (x : ↥ComplexMatrix2.traceless) : Prop :=
  ComplexMatrix2.operatorNorm (x : ComplexMatrix2) ≤ pivotInnerScale L ∧
    complexBlockAverage (twistedConfig c (extendAtPivot c a' x) V) c =
      complexBlockAverage V c
def pivotSourceAt (c : BondAtLevel L m K (n + 1)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (a' : LieBondField (setWithoutPivot c)) : ↥ComplexMatrix2.traceless :=
  Classical.epsilon (IsPivotEquationSolution c V a')
end YangMills.Construction.PeriodicLattice
