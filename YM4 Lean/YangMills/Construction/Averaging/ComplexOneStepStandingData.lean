import YangMills.Construction.Lattice.NumbersOfTheStraightenedAverage
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsInTheToolbox
import Mathlib
set_option autoImplicit false
universe u v w
noncomputable section
namespace YangMills.Construction.Averaging.ComplexStepSetting
abbrev radius (L : ℕ) : ℝ := PeriodicLattice.admissibleStepRadius L
abbrev bondRadius (L : ℕ) : ℝ := PeriodicLattice.bondFieldRadius L
abbrev curvatureBound (L : ℕ) : ℝ := PeriodicLattice.plaquetteSmallness L
abbrev boundConstant (L : ℕ) : ℝ := PeriodicLattice.stepBoundConstant L
abbrev straightenedCurvatureConstant (L : ℕ) : ℝ :=
  PeriodicLattice.straightenedCurvatureThreshold L
abbrev straightenedRadiusConstant (L : ℕ) : ℝ := PeriodicLattice.straightenedRadius L
end YangMills.Construction.Averaging.ComplexStepSetting
end
