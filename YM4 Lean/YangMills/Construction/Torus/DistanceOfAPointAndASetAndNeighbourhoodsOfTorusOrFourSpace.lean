import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable (s : Conventions.StandingParameters) (E : Ambient)
def distToSet (x : Pt s E) (A : Set (Pt s E)) : ℝ≥0∞ := setDist s E {x} A
def openThickening (S : Set (Pt s E)) (η : ℝ) : Set (Pt s E) :=
  {x | distToSet s E x S < ENNReal.ofReal η}
def closedThickening (S : Set (Pt s E)) (η : ℝ) : Set (Pt s E) :=
  {x | distToSet s E x S ≤ ENNReal.ofReal η}
end YangMills.Construction.AmbientPoints
