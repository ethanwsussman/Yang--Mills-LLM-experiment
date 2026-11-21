import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def TopEdgesAndCubes : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ y : Vertex L n k k, cellDist y y = 0) ∧
    (∀ e : Edge L n k k, cellDist e.source e.target ≤ 2) ∧
    ∀ (y y' : Vertex L n k k) (p : PeriodicLattice.FourTorus L n),
      p ∈ PeriodicLattice.refinedBlock k y → p ∈ PeriodicLattice.refinedBlock k y' → y = y'
end RunningCouplingSlope
end YangMills.Construction
end
