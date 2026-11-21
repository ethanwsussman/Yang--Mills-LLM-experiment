import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open AmbientPoints (Pt)
namespace LipschitzClasses
def toKind : Ambient → PeriodicSpace.Kind
  | .torus => .torus
  | .euclidean => .euclidean
variable (s : Conventions.StandingParameters) (M : ℝ) (hM : 1 ≤ M)
abbrev params : PeriodicSpace.Params := .ofStanding s M hM
def lipTuplesSepRadius (n : ℕ) (d R : ℝ) :
    (E : Ambient) → Set (Fin n → Pt s E → ℝ)
  | .torus =>
    PeriodicSpace.Kind.lipTuplesSpacedInBalls (params s M hM) .torus n d R
  | .euclidean =>
    PeriodicSpace.Kind.lipTuplesSpacedInBalls (params s M hM) .euclidean
      n d R
end LipschitzClasses
end YangMills.Construction
end
