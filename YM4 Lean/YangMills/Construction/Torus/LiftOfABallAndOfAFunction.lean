import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Torus.IntegralOverTheTorus
import YangMills.Construction.Torus.LiftsOfBallsFunctionsAndTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestFunctions.BallLift
open Set TorusMetric PeriodicLattice Conventions
def projIsometricOnBall (P : StandingParameters) (z : P.Torus) (ρ : ℝ) (c : Fin 4 → ℝ) : Prop :=
  (∀ x ∈ closedBallR4 c ρ, ∀ y ∈ closedBallR4 c ρ,
      torusEuclidNorm (torusProj (torusSide P.L P.m) x - torusProj (torusSide P.L P.m) y) =
        euclidNormVec (x - y)) ∧
    BijOn (torusProj (torusSide P.L P.m)) (closedBallR4 c ρ)
      (closedBallTorus (ℓ := torusSide P.L P.m) z ρ)
def liftProperties (P : StandingParameters) (ρ : ℝ) (c : Fin 4 → ℝ) (f : P.Torus → ℝ)
    (g : (Fin 4 → ℝ) → ℝ) : Prop :=
  BijOn (torusProj (torusSide P.L P.m)) {x | g x ≠ 0} {w | f w ≠ 0} ∧
    BijOn (torusProj (torusSide P.L P.m)) (euclidSupport g) (metricSupport f) ∧
    IsCompact (euclidSupport g) ∧ euclidSupport g ⊆ closedBallR4 c ρ ∧
    euclidSupNorm g = torusSupNorm f ∧
    ((∀ w, 0 ≤ f w) → ∀ x, 0 ≤ g x) ∧
    (@Measurable _ _ (borelSets P.L P.m) _ f → Measurable g)
def liftPairProperties (P : StandingParameters) (f f' : P.Torus → ℝ)
    (g g' : (Fin 4 → ℝ) → ℝ) : Prop :=
  setDistR4 (euclidSupport g) (euclidSupport g') =
      setEuclidDist (S := torusSide P.L P.m) (metricSupport f) (metricSupport f') ∧
    (Disjoint (metricSupport f) (metricSupport f') →
      Disjoint (euclidSupport g) (euclidSupport g'))
def BallAndFunctionLift : Prop :=
  ∀ (P : StandingParameters) (z : P.Torus) (ρ : ℝ) (c : Fin 4 → ℝ),
    IsAdmissibleRadius P.L P.m ρ → c ∈ liftsOf z →
      projIsometricOnBall P z ρ c ∧
      (∀ (f : P.Torus → ℝ) (g : (Fin 4 → ℝ) → ℝ),
        IsFunctionLift z ρ c f g → liftProperties P ρ c f g) ∧
      ∀ (f f' : P.Torus → ℝ) (g g' : (Fin 4 → ℝ) → ℝ),
        IsFunctionLift z ρ c f g → IsFunctionLift z ρ c f' g' →
          liftPairProperties P f f' g g'
end YangMills.Construction.TestFunctions.BallLift
end
