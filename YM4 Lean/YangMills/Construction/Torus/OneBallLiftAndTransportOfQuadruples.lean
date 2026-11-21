import YangMills.Construction.Torus.GeometryOfASeparatedQuadruple
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.QuadrupleBalls
def IsCenterFamilyR4 (d : ℝ) (f : Fin 4 → (Fin 4 → ℝ) → ℝ) (x : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i, PlaquetteSupports.euclideanTSupport (f i) ⊆ TestFunctions.closedBallR4 (x i) d
def OneBallPropertyR4 (d : ℝ) (f : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i, ∃ t, f i t ≠ 0) ∧ (∃ x, IsCenterFamilyR4 d f x) ∧
    ∀ x, IsCenterFamilyR4 d f x →
      (∀ i j, i ≠ j →
        ENNReal.ofReal d ≤ TestFunctions.setDistR4 (PlaquetteSupports.euclideanTSupport (f i))
            (PlaquetteSupports.euclideanTSupport (f j)) ∧
          TestFunctions.setDistR4 (PlaquetteSupports.euclideanTSupport (f i))
            (PlaquetteSupports.euclideanTSupport (f j)) ≤ ENNReal.ofReal (6 * d)) ∧
      (∀ i, TestFunctions.euclidDistR4 (x i) (x 0) ≤ 8 * d) ∧
      ∀ i, PlaquetteSupports.euclideanTSupport (f i) ⊆ TestFunctions.closedBallR4 (x 0) (9 * d)
section Torus
variable {s : Conventions.StandingParameters}
def IsCenterFamilyTorus (d : ℝ) (f : Fin 4 → s.Torus → ℝ) (x : Fin 4 → s.Torus) : Prop :=
  ∀ i, PlaquetteSupports.torusTSupport (f i) ⊆ QuadrupleGeometry.ballOnTorus (x i) d
def OneBallPropertyTorus (d : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  (∀ i, ∃ u, f i u ≠ 0) ∧ (∃ x, IsCenterFamilyTorus d f x) ∧
    ∀ x, IsCenterFamilyTorus d f x →
      (∀ i j, i ≠ j →
        ENNReal.ofReal d ≤ TorusMeasure.setDist (PlaquetteSupports.torusTSupport (f i))
            (PlaquetteSupports.torusTSupport (f j)) ∧
          TorusMeasure.setDist (PlaquetteSupports.torusTSupport (f i))
            (PlaquetteSupports.torusTSupport (f j)) ≤ ENNReal.ofReal (6 * d)) ∧
      (∀ i, TorusMeasure.pointDist (x i) (x 0) ≤ 8 * d) ∧
      ∀ i, PlaquetteSupports.torusTSupport (f i) ⊆ QuadrupleGeometry.ballOnTorus (x 0) (9 * d)
def BallLiftProperty (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  ∀ (x : Fin 4 → s.Torus) (c : Fin 4 → ℝ), IsCenterFamilyTorus d f x →
    TorusMeasure.proj s c = x 0 →
    QuadrupleGeometry.IsBallIsometry c (x 0) d ∧
      QuadrupleClasses.IsBallLift s d ϑ f (fun i => QuadrupleClasses.ballLift s d c (f i)) ∧
      (fun i => QuadrupleClasses.ballLift s d c (f i)) ∈ QuadrupleClasses.quadsR4 d ϑ
def LiftsDifferByPeriod (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) : Prop :=
  ∀ g g', QuadrupleClasses.IsBallLift s d ϑ f g → QuadrupleClasses.IsBallLift s d ϑ f g' →
    ∃ k : Fin 4 → ℤ, ∀ (i : Fin 4) (t : Fin 4 → ℝ),
      g' i t = g i (t - TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)
def IsDeterminedByLifts (d ϑ : ℝ) (f : Fin 4 → s.Torus → ℝ) (A : Set (Fin 4 → s.Torus → ℝ))
    (B : Set (Fin 4 → (Fin 4 → ℝ) → ℝ)) : Prop :=
  (f ∈ A ↔ ∃ g, QuadrupleClasses.IsBallLift s d ϑ f g ∧ g ∈ B) ∧
    (f ∈ A ↔ ∀ g, QuadrupleClasses.IsBallLift s d ϑ f g → g ∈ B)
end Torus
def PeriodizationsMapInto (s : Conventions.StandingParameters)
    (B : Set (Fin 4 → (Fin 4 → ℝ) → ℝ)) (A : Set (Fin 4 → s.Torus → ℝ)) : Prop :=
  ∀ f ∈ B, (∀ i, ∃ S, TestFunctions.IsPeriodizable (PeriodicLattice.torusSide s.L s.m) S (f i)) ∧
    (fun i => TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (f i)) ∈ A ∧
    ∀ i, TestFunctions.uniformNorm (TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (f i)) =
      TestFunctions.uniformNorm (f i)
def PropertiesR4 (d ϑ : ℝ) : Prop :=
  QuadrupleClasses.collinearQuadsR4 d ϑ ⊆ QuadrupleClasses.quadsR4 d ϑ ∧
    ∀ f ∈ QuadrupleClasses.quadsR4 d ϑ, OneBallPropertyR4 d f
def PropertiesTorus (s : Conventions.StandingParameters) (d ϑ : ℝ) : Prop :=
  QuadrupleClasses.collinearQuadsTorus s d ϑ ⊆ QuadrupleClasses.quadsTorus s d ϑ ∧
    9 * d < PeriodicLattice.torusSide s.L s.m / 4 ∧
    ∀ f ∈ QuadrupleClasses.quadsTorus s d ϑ, OneBallPropertyTorus d f ∧ BallLiftProperty d ϑ f ∧
      LiftsDifferByPeriod d ϑ f ∧
      IsDeterminedByLifts d ϑ f (QuadrupleClasses.shapeQuadsTorus s d ϑ)
        (QuadrupleClasses.shapeQuadsR4 d ϑ) ∧
      IsDeterminedByLifts d ϑ f (QuadrupleClasses.collinearQuadsTorus s d ϑ)
        (QuadrupleClasses.collinearQuadsR4 d ϑ)
def BallLiftPeriodizationStatement : Prop :=
  ∀ d ϑ : ℝ, 0 < d → ϑ ∈ Ioc (0 : ℝ) 1 →
    PropertiesR4 d ϑ ∧
      ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
        PropertiesTorus s d ϑ ∧
          PeriodizationsMapInto s (QuadrupleClasses.collinearQuadsR4 d ϑ)
            (QuadrupleClasses.collinearQuadsTorus s d ϑ) ∧
          PeriodizationsMapInto s (QuadrupleClasses.shapeQuadsR4 d ϑ)
            (QuadrupleClasses.shapeQuadsTorus s d ϑ)
end YangMills.Construction.QuadrupleBalls
