import YangMills.Construction.InfiniteLattice.CutoffMotionsAndPlaquetteSquares
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.TimeReflections
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def LatticeSymmetry.mapSquare (r : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    Set AmbientSpace :=
  p.squareImage r.toFun
def equalTimePlane (t : ℝ) : Set AmbientSpace := {x | x timeAxis = t}
def reflectTime (t : ℝ) : AmbientSpace → AmbientSpace := coordinateReflection timeAxis t
theorem timeReflect_toFun_eq (t : halfSpacingTimes a) :
    (timeReflect t).toFun = reflectTime t := by
  funext x
  rw [timeReflect_apply]
  rfl
def timeConj (t : halfSpacingTimes a) (B : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conj ((timeReflect t).actOn B U)
end InfiniteLattice
end YangMills.Construction
