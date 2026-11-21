import YangMills.Construction.Constants.HessianNumerals
import YangMills.Construction.Lattice.CommutatorsOfTheSystemWithAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedCommutatorConstants
def averageFactor (L : ℕ) : ℝ :=
  1 + 2 * PeriodicLattice.complexBackgroundLinearConstant L * PeriodicLattice.complexBackgroundRadius L
def functionPartConstant (L : ℕ) : ℝ :=
  max
    (4 + 5 * (L : ℝ) * Constants.Hessian.curvatureFactor + 160 * averageFactor L ^ 2 * (L : ℝ) ^ 2 +
      160 * PeriodicLattice.complexBackgroundKernelConstant L * (L : ℝ) ^ 2)
    (max (3 * (L : ℝ) ^ 2 * SequenceTriples.commutatorBoundConstant L + 12 * (L : ℝ) + 24)
      (2 + 4 * (L : ℝ) ^ 4 + 192 * PeriodicLattice.complexBackgroundKernelConstant L * (L : ℝ)))
def weightedCommutatorConstant (L : ℕ) : ℝ :=
  max (SequenceTriples.commutatorBoundConstant L + functionPartConstant L)
    (9 * (L : ℝ) ^ 2 + 21 * (L : ℝ) + 2)
end YangMills.Construction.WeightedCommutatorConstants
end
