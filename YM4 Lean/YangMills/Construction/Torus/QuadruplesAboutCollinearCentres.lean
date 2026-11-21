import YangMills.Construction.Torus.BumpOnFourSpaceAndCollinearAndSpacingConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.QuadrupleClasses.CollinearCentres
open Collinear
def equallySpacedPoints (y e : Fin 4 → ℝ) (t d : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i => y + (((i : ℕ) : ℝ) * t * d) • e
def rescaledBump (d : ℝ) : (Fin 4 → ℝ) → ℝ := fun x => QuadrupleClasses.radialBumpR4 ((16 / d) • x)
def bumpsCentredAt (d : ℝ) (c : Fin 4 → Fin 4 → ℝ) : Fin 4 → (Fin 4 → ℝ) → ℝ :=
  Collinear.translateFamily (rescaledBump d) c
def HasShapeAxisAlongCentres (d : ℝ) (g : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∃ (e : Fin 4 → ℝ) (c : Fin 4 → Fin 4 → ℝ), QuadrupleClasses.IsLineDirection e c ∧
    (∀ i, PlaquetteSupports.euclideanTSupport (g i) ⊆ TestFunctions.closedBallR4 (c i) (d / 16)) ∧
    QuadrupleClasses.IsShapeAxis e g
def CollinearSubsetShapeR4 (d θ : ℝ) : Prop :=
  QuadrupleClasses.collinearQuadsR4 d θ ⊆ QuadrupleClasses.shapeQuadsR4 d θ ∧
    ∀ g ∈ QuadrupleClasses.collinearQuadsR4 d θ, HasShapeAxisAlongCentres d g
def CollinearSubsetShapeTorus (s : Conventions.StandingParameters) (d θ : ℝ) : Prop :=
  QuadrupleClasses.collinearQuadsTorus s d θ ⊆ QuadrupleClasses.shapeQuadsTorus s d θ ∧
    ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d θ, ∃ g, QuadrupleClasses.IsBallLift s d θ f g ∧
      g ∈ QuadrupleClasses.collinearQuadsR4 d θ ∧ HasShapeAxisAlongCentres d g
def BumpsInCollinearClassR4 (d θ : ℝ) (y e : Fin 4 → ℝ) (t : ℝ) : Prop :=
  PlaquetteSupports.euclideanTSupport (rescaledBump d) = TestFunctions.closedBallR4 0 (d / 16) ∧
    (∀ i, TestFunctions.IsC1R4 (bumpsCentredAt d (equallySpacedPoints y e t d) i)) ∧
    bumpsCentredAt d (equallySpacedPoints y e t d) ∈ QuadrupleClasses.collinearQuadsR4 d θ
def PeriodizedBumpsInCollinearClassTorus (s : Conventions.StandingParameters) (d θ : ℝ) (y e : Fin 4 → ℝ) (t : ℝ) : Prop :=
  (∀ i, TestFunctions.IsPeriodizable (PeriodicLattice.torusSide s.L s.m)
    (TestFunctions.closedBallR4 (equallySpacedPoints y e t d 0) (9 * d)) (bumpsCentredAt d (equallySpacedPoints y e t d) i)) ∧
    Collinear.periodizedQuad s (bumpsCentredAt d (equallySpacedPoints y e t d)) ∈ QuadrupleClasses.collinearQuadsTorus s d θ
def CollinearCentresStatement : Prop :=
  (∀ d θ : ℝ, TestFunctions.IsScaleShape d θ →
    Collinear.IsShapeAxisOfCollinearCentres d θ ∧ CollinearSubsetShapeR4 d θ ∧
      ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
        CollinearSubsetShapeTorus s d θ) ∧
    Collinear.collinearThetaBound = Real.pi ^ 2 / (12 * 16 ^ 4) ∧ 0 < Collinear.collinearThetaBound ∧
    Collinear.collinearThetaBound < (16 : ℝ) ^ (-4 : ℤ) ∧
    ∀ d θ : ℝ, TestFunctions.IsScaleShape d θ → QuadrupleClasses.CollinearThetaCondition θ →
      ∀ (y e : Fin 4 → ℝ) (t : ℝ), TorusMetric.euclidNormVec e = 1 → QuadrupleClasses.SpacingCondition t →
        BumpsInCollinearClassR4 d θ y e t ∧
          ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
            PeriodizedBumpsInCollinearClassTorus s d θ y e t
end YangMills.Construction.QuadrupleClasses.CollinearCentres
end
