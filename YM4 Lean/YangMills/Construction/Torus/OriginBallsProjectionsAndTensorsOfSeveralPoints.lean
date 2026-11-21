import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
def kindOf : Ambient → PeriodicSpace.Kind
  | .torus => .torus
  | .euclidean => .euclidean
def paramsOf (s : Conventions.StandingParameters) : PeriodicSpace.Params :=
  PeriodicSpace.Params.ofStanding s 1 le_rfl
def ptEquiv (s : Conventions.StandingParameters) :
    (E : Ambient) → Pt s E ≃ (kindOf E).Pt (paramsOf s)
  | .torus => Equiv.refl _
  | .euclidean => Equiv.refl _
variable (s : Conventions.StandingParameters) (E : Ambient)
def origin : Pt s E := proj s E 0
def originBall (ρ : ℝ≥0∞) : Set (Pt s E) :=
  if ρ = ∞ then univ else openBall s E (origin s E) ρ.toReal
variable {s E}
end AmbientPoints
end YangMills.Construction
