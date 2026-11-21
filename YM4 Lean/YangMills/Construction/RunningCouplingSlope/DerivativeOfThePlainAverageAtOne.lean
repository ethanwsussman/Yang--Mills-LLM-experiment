import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices Conventions
def NormalizedMeanAtOne : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ m k j : ℕ, 0 < m → j < k → ∀ B ∈ edgeFormSpace L m k j,
    ∀ e : Edge L m k (j + 1), e.IsPositivelyOriented →
      contourMean (fun _ : Edge L m k j => (1 : ComplexMatrix2)) e = 1 ∧
      meanRadius (fun _ : Edge L m k j => (1 : ComplexMatrix2)) e = 1 ∧
      normalizedMean (fun _ : Edge L m k j => (1 : ComplexMatrix2)) e = 1 ∧
      HasDerivAt (fun t : ℝ => meanRadius
        (PeriodicLattice.expTwist ((t : ℂ) • B) fun _ => (1 : ComplexMatrix2)) e) 0 0 ∧
      leftDifferential normalizedMean (fun _ => 1) B e = linearSmoothing L m k j B e
end YangMills.Construction.RunningCouplingSlope
end
