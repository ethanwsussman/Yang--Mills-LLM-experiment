import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def NeighbouringFineVertexCells : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ,
    (∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0),
      (x : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.refinedBlock k (fineVertexCell (L := L) (n := n) (k := k) x)) ∧
    ∀ (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4
end RunningCouplingSlope
end YangMills.Construction
end
