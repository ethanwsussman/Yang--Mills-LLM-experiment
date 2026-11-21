import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def LinearSmoothingContourFormula : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ (A : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
      linearSmoothing L n k j A c = ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
          ∑ π : Equiv.Perm (Fin 4), (PeriodicLattice.bondFormSumAlong A (contourLeg c.source x π) +
            PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
            PeriodicLattice.bondFormSumAlong A
              (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))
end YangMills.Construction.RunningCouplingSlope
end
