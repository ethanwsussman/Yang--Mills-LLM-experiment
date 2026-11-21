import YangMills.Construction.RunningCouplingSlope.TriplesCarriedByACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def CellDistBlockBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ y y' : Vertex L n k k, 0 ≤ cellDist y y') ∧
    (∀ y : Vertex L n k k, cellDist y y = 0) ∧
    (∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : Vertex L n k k, cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ j < k, ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        cellDist (levelVertexCell x) (levelVertexCell y) ≤ 3) ∧
    ∀ j ≤ k, ∀ b : Edge L n k j,
      cellDist (levelVertexCell b.source) (levelVertexCell b.target) ≤ 4
end RunningCouplingSlope
end YangMills.Construction
end
