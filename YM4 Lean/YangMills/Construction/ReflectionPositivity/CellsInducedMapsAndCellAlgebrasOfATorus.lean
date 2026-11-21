import YangMills.Construction.ReflectionPositivity.FacePlanesCellGroupAndCellsOfACellSide
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.PeriodicCubes
open InfiniteLattice (AmbientSpace)
variable (L m K : ℕ) (lc : ℝ)
variable {L m K lc}
def InducedBy (rbar : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m)
    (r : AmbientSpace → AmbientSpace) : Prop :=
  TorusLifts.Descends (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m) r rbar
variable (L m K lc)
def inducedReflections : Set (PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m) :=
  {rbar | ∃ r ∈ FaceReflections.reflectionGroup L K lc, InducedBy rbar r}
variable {L m K lc}
end YangMills.Construction.ReflectionPositivity.PeriodicCubes
