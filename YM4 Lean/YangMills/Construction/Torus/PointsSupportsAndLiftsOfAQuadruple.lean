import YangMills.Construction.Torus.LiftsOfBallsFunctionsAndTuples
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric TestFunctions TorusMeasure PlaquetteSupports QuadrupleClasses
namespace QuadrupleGeometry
def HasWitnessPointsR4 (d ϑ : ℝ) (f : Fin 4 → (Fin 4 → ℝ) → ℝ) (x : Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i, euclideanTSupport (f i) ⊆ closedBallR4 (x i) d ∧
    ϑ * uniformNorm (f i) * d ^ 4 ≤ integralR4 (f i) ∧
    lipConstR4 (f i) ≤ uniformNorm (f i) / (ϑ * d)) ∧
  ∀ i j, i ≠ j →
    ENNReal.ofReal d ≤ setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ∧
      setDistR4 (euclideanTSupport (f i)) (euclideanTSupport (f j)) ≤ ENNReal.ofReal (6 * d)
def MemQuadsR4Iff (d ϑ : ℝ) : Prop :=
  ∀ f : Fin 4 → (Fin 4 → ℝ) → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i) ∧ ∀ t, 0 ≤ f i t) →
    (f ∈ quadsR4 d ϑ ↔ (∀ i, ∃ t, f i t ≠ 0) ∧ ∃ x, HasWitnessPointsR4 d ϑ f x)
def WitnessGeometryR4 (d ϑ : ℝ) : Prop :=
  ∀ f ∈ quadsR4 d ϑ, ∀ x, HasWitnessPointsR4 d ϑ f x →
    (∀ i j, i ≠ j → euclidDistR4 (x i) (x j) ≤ 8 * d) ∧
    (∀ i j, i ≠ j → ∀ u ∈ euclideanTSupport (f i), ∀ v ∈ euclideanTSupport (f j),
      d ≤ euclidDistR4 u v ∧ euclidDistR4 u v ≤ 10 * d) ∧
    (∀ i, euclideanTSupport (f i) ⊆ closedBallR4 (x 0) (9 * d)) ∧
    (∀ i, IsCompact (euclideanTSupport (f i))) ∧
    ∀ i j, i ≠ j → Disjoint (euclideanTSupport (f i)) (euclideanTSupport (f j))
section OnTorus
variable {s : Conventions.StandingParameters}
def HasWitnessPointsTorus (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) (x : Fin 4 → s.Torus) : Prop :=
  (∀ i, torusTSupport (f i) ⊆ closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (x i) d ∧
    ϑ * uniformNorm (f i) * d ^ 4 ≤ torusIntegral (f i) ∧
    lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (f i) ≤ uniformNorm (f i) / (ϑ * d)) ∧
  ∀ i j, i ≠ j →
    ENNReal.ofReal d ≤ setDist (torusTSupport (f i)) (torusTSupport (f j)) ∧
      setDist (torusTSupport (f i)) (torusTSupport (f j)) ≤ ENNReal.ofReal (6 * d)
end OnTorus
def MemQuadsTorusIff (s : Conventions.StandingParameters) (d ϑ : ℝ) : Prop :=
  ∀ f : Fin 4 → s.Torus → ℝ,
    (∀ i, IsLipschitzFor (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m)) (f i) ∧
      ∀ u, 0 ≤ f i u) →
    (f ∈ quadsTorus s d ϑ ↔ (∀ i, ∃ u, f i u ≠ 0) ∧ ∃ x, HasWitnessPointsTorus d ϑ f x)
def WitnessGeometryTorus (s : Conventions.StandingParameters) (d ϑ : ℝ) : Prop :=
  ∀ f ∈ quadsTorus s d ϑ, ∀ x, HasWitnessPointsTorus d ϑ f x →
    (∀ i j, i ≠ j → pointDist (x i) (x j) ≤ 8 * d) ∧
    (∀ i j, i ≠ j → ∀ u ∈ torusTSupport (f i), ∀ v ∈ torusTSupport (f j),
      d ≤ pointDist u v ∧ pointDist u v ≤ 10 * d) ∧
    (∀ i, torusTSupport (f i) ⊆ closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (x 0) (9 * d)) ∧
    (∀ i, IsCompact (torusTSupport (f i))) ∧
    ∀ i j, i ≠ j → Disjoint (torusTSupport (f i)) (torusTSupport (f j))
def quadLift (s : Conventions.StandingParameters) (d : ℝ) (c : Fin 4 → ℝ) (f : Fin 4 → s.Torus → ℝ) :
    Fin 4 → (Fin 4 → ℝ) → ℝ :=
  fun i => ballLift s d c (f i)
def BallLiftProperties (s : Conventions.StandingParameters) (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ)
    (c : Fin 4 → ℝ) : Prop :=
  proj s '' closedBallR4 c (9 * d) =
      closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (proj s c) (9 * d) ∧
    IsClosedBallLift (L := s.L) (m := s.m) (proj s c) (9 * d) (closedBallR4 c (9 * d)) ∧
    SupportsInBall (L := s.L) (m := s.m) (proj s c) (9 * d) f ∧
    (∀ i, IsFunctionLift (L := s.L) (m := s.m) (proj s c) (9 * d) c (f i)
      (quadLift s d c f i)) ∧
    IsBallLift s d ϑ f (quadLift s d c f) ∧
    quadLift s d c f ∈ quadsR4 d ϑ ∧
    ∀ i, IsPeriodizable (PeriodicLattice.torusSide s.L s.m) (closedBallR4 c (9 * d))
        (quadLift s d c f i) ∧
      f i = periodize (PeriodicLattice.torusSide s.L s.m) (quadLift s d c f i) ∧
      integralR4 (quadLift s d c f i) = torusIntegral (f i) ∧
      uniformNorm (quadLift s d c f i) = uniformNorm (f i)
def TorusLiftFacts (s : Conventions.StandingParameters) (d ϑ : ℝ) : Prop :=
  ∀ f ∈ quadsTorus s d ϑ,
    (∀ x, HasWitnessPointsTorus d ϑ f x → ∀ c, proj s c = x 0 →
      ∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) ∧
    (∀ c, (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) →
      BallLiftProperties s d ϑ f c) ∧
    (∀ g, IsTupleLift (L := s.L) (m := s.m) f g →
      ∃ c, (∀ i, torusTSupport (f i) ⊆ proj s '' closedBallR4 c (9 * d)) ∧
        g = quadLift s d c f) ∧
    ∀ g, IsTupleLift (L := s.L) (m := s.m) f g ↔ IsBallLift s d ϑ f g
def FactsR4 : Prop :=
  ∀ d ϑ : ℝ, 0 < d → ϑ ∈ Ioc (0 : ℝ) 1 → MemQuadsR4Iff d ϑ ∧ WitnessGeometryR4 d ϑ
def FactsTorus : Prop :=
  ∀ (s : Conventions.StandingParameters) (d ϑ : ℝ), 0 < d → ϑ ∈ Ioc (0 : ℝ) 1 →
    40 * d ≤ PeriodicLattice.torusSide s.L s.m →
      MemQuadsTorusIff s d ϑ ∧ WitnessGeometryTorus s d ϑ ∧
        9 * d < PeriodicLattice.torusSide s.L s.m / 4 ∧ TorusLiftFacts s d ϑ
def Statement : Prop := FactsR4 ∧ FactsTorus
end QuadrupleGeometry
end YangMills.Construction
