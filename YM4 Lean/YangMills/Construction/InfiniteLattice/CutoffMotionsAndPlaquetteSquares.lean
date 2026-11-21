import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
abbrev cutoffLatticeMotions (L K : ℕ) : Set (AmbientSpace → AmbientSpace) :=
  affineHyperoctahedralMaps (PeriodicLattice.meshSize L (K : ℤ))
def ElementaryPlaquette.closedSquare (p : ElementaryPlaquette a) : Set AmbientSpace :=
  {y | ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, y = (p.corner : AmbientSpace) +
    a • (t • (Pi.single p.lowAxis 1 : AmbientSpace) + t' • (Pi.single p.highAxis 1 : AmbientSpace))}
def ElementaryPlaquette.squareImage (r : AmbientSpace → AmbientSpace) (p : ElementaryPlaquette a) :
    Set AmbientSpace :=
  r '' p.closedSquare
end YangMills.Construction.InfiniteLattice
