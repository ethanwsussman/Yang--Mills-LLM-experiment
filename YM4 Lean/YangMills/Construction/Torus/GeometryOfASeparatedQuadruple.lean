import YangMills.Construction.Torus.OneFunctionConditions
import YangMills.Construction.Torus.SeparatedQuadruples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.QuadrupleGeometry
open Set TestFunctions TorusMeasure PlaquetteSupports BumpConditions QuadrupleClasses
noncomputable section
def SupportGapsR4 (d ϑ : ℝ) (f : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i, ∃ t, f i t ≠ 0) ∧ (∀ i, ∃ x, SatisfiesR4 x d ϑ (f i)) ∧
    ∀ i j, i ≠ j →
      ENNReal.ofReal d ≤ setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ∧
        setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ≤ ENNReal.ofReal (6 * d)
def PointGapsAndBallR4 (d ϑ : ℝ) (f : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ u ∈ euclideanTSupport (f i), ∀ v ∈ euclideanTSupport (f j),
      d ≤ euclidDistR4 u v ∧ euclidDistR4 u v ≤ 10 * d) ∧
    (∃ x, ∀ i, euclideanTSupport (f i) ⊆ closedBallR4 x (9 * d)) ∧
    ∀ x₁, SatisfiesR4 x₁ d ϑ (f 0) → ∀ i, euclideanTSupport (f i) ⊆ closedBallR4 x₁ (9 * d)
section OnTorus
variable {s : Conventions.StandingParameters}
def ballOnTorus (y : s.Torus) (r : ℝ) : Set s.Torus :=
  closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) y r
def SupportGapsTorus (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  (∀ i, ∃ u, f i u ≠ 0) ∧ (∀ i, ∃ x, SatisfiesTorus x d ϑ (f i)) ∧
    ∀ i j, i ≠ j →
      ENNReal.ofReal d ≤ setDist (torusTSupport (f i)) (torusTSupport (f j)) ∧
        setDist (torusTSupport (f i)) (torusTSupport (f j)) ≤ ENNReal.ofReal (6 * d)
def PointGapsAndBallTorus (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ u ∈ torusTSupport (f i), ∀ v ∈ torusTSupport (f j),
      d ≤ pointDist u v ∧ pointDist u v ≤ 10 * d) ∧
    (∃ x, ∀ i, torusTSupport (f i) ⊆ ballOnTorus x (9 * d)) ∧
    ∀ x₁, SatisfiesTorus x₁ d ϑ (f 0) → ∀ i, torusTSupport (f i) ⊆ ballOnTorus x₁ (9 * d)
def liftOverBall (c : Fin 4 → ℝ) (d : ℝ) (f : s.Torus → ℝ) : (Fin 4 → ℝ) → ℝ :=
  liftToBall (PeriodicLattice.torusSide s.L s.m) c (9 * d) f
def BallImagesCover (s : Conventions.StandingParameters) (d : ℝ) : Prop :=
  9 * d ≤ PeriodicLattice.torusSide s.L s.m / 4 ∧
    ∀ (y : s.Torus) (t : Fin 4 → ℝ), IsLift s y t →
      proj s '' closedBallR4 t (9 * d) = ballOnTorus y (9 * d)
def IsBallIsometry (c : Fin 4 → ℝ) (y : s.Torus) (d : ℝ) : Prop :=
  BijOn (proj s) (closedBallR4 c (9 * d)) (ballOnTorus y (9 * d)) ∧
    ∀ t ∈ closedBallR4 c (9 * d), ∀ t' ∈ closedBallR4 c (9 * d),
      pointDist (proj s t) (proj s t') = euclidDistR4 t t'
def LiftMatches (c : Fin 4 → ℝ) (d : ℝ) (f : s.Torus → ℝ) : Prop :=
  IsPeriodizable (PeriodicLattice.torusSide s.L s.m) (closedBallR4 c (9 * d)) (liftOverBall c d f) ∧
    f = periodize (PeriodicLattice.torusSide s.L s.m) (liftOverBall c d f) ∧
    uniformNorm (liftOverBall c d f) = uniformNorm f ∧
    lipConstR4 (liftOverBall c d f) = lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f ∧
    integralR4 (liftOverBall c d f) = torusIntegral f ∧
    proj s '' euclideanTSupport (liftOverBall c d f) = torusTSupport f
def LiftsOverBall (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  ∀ (y : s.Torus) (c : Fin 4 → ℝ), (∀ i, torusTSupport (f i) ⊆ ballOnTorus y (9 * d)) →
    proj s '' closedBallR4 c (9 * d) = ballOnTorus y (9 * d) →
    IsBallIsometry c y d ∧ (fun i => liftOverBall c d (f i)) ∈ quadsR4 d ϑ ∧
      ∀ i, LiftMatches c d (f i)
def LiftsDifferByPeriod (d : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  ∀ c c' : Fin 4 → ℝ, (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) →
    (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c' (9 * d)) →
    ∃ k : Fin 4 → ℤ, ∀ (t : Fin 4 → ℝ) (i : Fin 4),
      liftOverBall c' d (f i) (t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) =
        liftOverBall c d (f i) t
end OnTorus
def PeriodizationIsQuadruple (s : Conventions.StandingParameters) (d ϑ : ℝ)
    (f : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i, ∃ S, IsPeriodizable (PeriodicLattice.torusSide s.L s.m) S (f i)) ∧
    (fun i => periodize (PeriodicLattice.torusSide s.L s.m) (f i)) ∈ quadsTorus s d ϑ
def GeometryOnR4 : Prop :=
  ∀ d ϑ : ℝ, 0 < d → ϑ ∈ Ioc (0 : ℝ) 1 → ∀ f ∈ quadsR4 d ϑ,
    SupportGapsR4 d ϑ f ∧ PointGapsAndBallR4 d ϑ f ∧
      ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
        PeriodizationIsQuadruple s d ϑ f
def GeometryOnTorus : Prop :=
  ∀ (s : Conventions.StandingParameters) (d ϑ : ℝ), 0 < d → ϑ ∈ Ioc (0 : ℝ) 1 →
    40 * d ≤ PeriodicLattice.torusSide s.L s.m → ∀ f ∈ quadsTorus s d ϑ,
      SupportGapsTorus d ϑ f ∧ PointGapsAndBallTorus d ϑ f ∧
        BallImagesCover s d ∧ LiftsOverBall d ϑ f ∧ LiftsDifferByPeriod d f
def QuadrupleGeometryStatement : Prop := GeometryOnR4 ∧ GeometryOnTorus
end
end YangMills.Construction.QuadrupleGeometry
