import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def faceEdges {L n k j : ℕ} (p : Face L n k j) : List (Edge L n k j) :=
  [PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis,
    PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis]
namespace FullSpace
def faceEdges {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) : List (InfiniteLattice.Link a) :=
  [InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
end FullSpace
end Tower
end YangMills.Construction
end
