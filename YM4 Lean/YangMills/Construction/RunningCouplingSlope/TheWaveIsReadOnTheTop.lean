import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def PlaneWaveRepresentsTorusField : Prop :=
  ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (B : edgeFormSpace L n k k),
      (B : Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k f → ∀ u : ℝ,
        RepresentsTorusField (PeriodicLattice.expTwist (u • (B : Edge L n k k → Matrices.ComplexMatrix2)) fun _ => 1)
          (SlopeCoefficient.expAlong (2 * L ^ n) (planeWaveOnTorus f) u)
end YangMills.Construction.RunningCouplingSlope
end
