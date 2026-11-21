import YangMills.Construction.Lattice.ContourPaths
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def AxisOrderLegsAreContours : Prop :=
  ∀ (L m : ℕ) (j j' : ℤ) (y : PeriodicLattice.Site L m j) (x : PeriodicLattice.Site L m j')
    (τ : Equiv.Perm (Fin 4)), ∃ σ : PeriodicLattice.AxisOrdering y x,
      PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x)
        (PeriodicLattice.Site.toSublattice y j')
        ((List.finRange 4).map τ) = PeriodicLattice.orderedContour y x σ
end RunningCouplingSlope
end YangMills.Construction
end
