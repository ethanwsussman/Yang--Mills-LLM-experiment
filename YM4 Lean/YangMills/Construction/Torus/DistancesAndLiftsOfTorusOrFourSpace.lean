import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.AmbientPoints.DistanceFacts
open YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
structure MetricFacts (s : Conventions.StandingParameters) (E : Ambient) : Prop where
  pointDist_proj_le : ∀ x x' : Fin 4 → ℝ,
    pointDist s E (proj s E x) (proj s E x') ≤ euclidNormVec (x - x')
  pointDist_proj_eq : ∀ x x' : Fin 4 → ℝ,
    ENNReal.ofReal (euclidNormVec (x - x')) < 2 * injRadius s E →
      pointDist s E (proj s E x) (proj s E x') = euclidNormVec (x - x')
  exists_lift_pointDist : ∀ (x : Fin 4 → ℝ) (y : Pt s E),
    ∃ x', IsLift s E y x' ∧ euclidNormVec (x - x') = pointDist s E (proj s E x) y
  isOpen_openBall : ∀ (y : Pt s E) (r : ℝ), 0 < r → IsOpen (openBall s E y r)
  setDiam_openBall_le : ∀ (y : Pt s E) (r : ℝ), 0 < r →
    setDiam s E (openBall s E y r) ≤ ENNReal.ofReal (2 * r)
  pointDist_comm : ∀ y y' : Pt s E, pointDist s E y y' = pointDist s E y' y
  eq_of_pointDist_eq_zero : ∀ y y' : Pt s E, pointDist s E y y' = 0 → y = y'
  pointDist_triangle : ∀ y y' y'' : Pt s E,
    pointDist s E y y'' ≤ pointDist s E y y' + pointDist s E y' y''
  setDiam_pos : ∀ A : Set (Pt s E), A.Nonempty → IsOpen A → 0 < setDiam s E A
def MetricFactsClaim : Prop := ∀ (s : Conventions.StandingParameters) (E : Ambient), MetricFacts s E
end
end YangMills.Construction.AmbientPoints.DistanceFacts
