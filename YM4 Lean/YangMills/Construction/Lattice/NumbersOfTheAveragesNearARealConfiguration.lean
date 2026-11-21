import YangMills.Construction.Lattice.AssertionsOfOneStepAtAComplexReference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def nearRealAverageBound (L : ℕ) : ℝ :=
  4 * (8 * Averaging.ComplexStepSetting.boundConstant L + 2)
def nearRealAverageRadius (L : ℕ) : ℝ :=
  min (Averaging.ComplexStepSetting.straightenedRadiusConstant L)
    (complexReferenceRadius L / nearRealAverageBound L)
end YangMills.Construction.PeriodicLattice
end
