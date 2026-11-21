import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TestFunctions TorusMetric TorusMeasure PlaquetteSupports Conventions
namespace QuadrupleClasses
namespace Collinear
def collinearThetaBound : ℝ := omega4 / (6 * 16 ^ 4)
def IsShapeAxisOfCollinearCentres (d θ : ℝ) : Prop :=
  ∀ (g : Fin 4 → (Fin 4 → ℝ) → ℝ) (e : Fin 4 → ℝ) (c : Fin 4 → Fin 4 → ℝ),
    g ∈ quadsR4 d θ → IsLineDirection e c →
      (∀ i, euclideanTSupport (g i) ⊆ closedBallR4 (c i) (d / 16)) → IsShapeAxis e g
def NestedClassesR4 (d θ : ℝ) : Prop :=
  collinearQuadsR4 d θ ⊆ shapeQuadsR4 d θ ∧
    shapeQuadsR4 d θ ⊆ quadsR4 d θ
def NestedClassesTorus (p : StandingParameters) (d θ : ℝ) : Prop :=
  collinearQuadsTorus p d θ ⊆ shapeQuadsTorus p d θ ∧
    shapeQuadsTorus p d θ ⊆ quadsTorus p d θ
def translateFamily (f : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → Fin 4 → ℝ) : Fin 4 → (Fin 4 → ℝ) → ℝ :=
  fun i x => f (x - c i)
def CollinearR4HasTranslates (d θ : ℝ) : Prop :=
  ∀ (a e : Fin 4 → ℝ), euclidNormVec e = 1 →
    ∃ (f : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → Fin 4 → ℝ),
      c 0 = a ∧ (∀ i, i ≠ 0 → c i - a ∈ realLine e) ∧
        (∀ x, x ∉ closedBallR4 0 (d / 16) → f x = 0) ∧
        (∀ i, IsC1R4 (translateFamily f c i)) ∧
        translateFamily f c ∈ collinearQuadsR4 d θ
def IntegralBoundR4 (d : ℝ) : Prop :=
  ∀ (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ), IsBoundedFun f → IsNullMeasurableFunR4 f →
    (∀ t, t ∉ closedBallR4 x (d / 16) → f t = 0) →
      integralR4 f ≤ omega4 * (d / 16) ^ 4 * uniformNorm f
def IntegralBoundTorus (p : StandingParameters) (d : ℝ) : Prop :=
  ∀ (f : p.Torus → ℝ) (x : p.Torus), IsBoundedFun f → IsMeasurableFun f →
    (∀ u, u ∉ closedBallTorus (ℓ := PeriodicLattice.torusSide p.L p.m) x (d / 16) → f u = 0) →
      torusIntegral f ≤ omega4 * (d / 16) ^ 4 * uniformNorm f
def BallLiftsAgree (p : StandingParameters) (d θ : ℝ) : Prop :=
  ∀ f ∈ quadsTorus p d θ, ∀ g g' : Fin 4 → (Fin 4 → ℝ) → ℝ,
    IsBallLift p d θ f g → IsBallLift p d θ f g' →
      (∀ e, IsShapeAxis e g → IsShapeAxis e g') ∧
        (g ∈ collinearQuadsR4 d θ → g' ∈ collinearQuadsR4 d θ)
def periodizedQuad (p : StandingParameters) (g : Fin 4 → (Fin 4 → ℝ) → ℝ) :
    Fin 4 → p.Torus → ℝ :=
  fun i => periodize (PeriodicLattice.torusSide p.L p.m) (g i)
def PeriodizationAgrees (p : StandingParameters) (d θ : ℝ) : Prop :=
  ∀ g ∈ quadsR4 d θ,
    IsBallLift p d θ (periodizedQuad p g) g ∧
      (periodizedQuad p g ∈ shapeQuadsTorus p d θ ↔
        g ∈ shapeQuadsR4 d θ) ∧
      (periodizedQuad p g ∈ collinearQuadsTorus p d θ ↔
        g ∈ collinearQuadsR4 d θ)
def CollinearQuadruplesStatement : Prop :=
  collinearThetaBound ∈ Ioc (0 : ℝ) 1 ∧
    volumeR4 (closedBallR4 0 (1 / 16)) = ENNReal.ofReal (omega4 * (16 : ℝ) ^ (-4 : ℤ)) ∧
    ∀ d θ : ℝ, IsScaleShape d θ →
      IsShapeAxisOfCollinearCentres d θ ∧ NestedClassesR4 d θ ∧
        (θ ≤ collinearThetaBound → CollinearR4HasTranslates d θ) ∧
        IntegralBoundR4 d ∧
        (omega4 * (16 : ℝ) ^ (-4 : ℤ) < θ → collinearQuadsR4 d θ = ∅) ∧
        ∀ p : StandingParameters, 40 * d ≤ PeriodicLattice.torusSide p.L p.m →
          NestedClassesTorus p d θ ∧ IntegralBoundTorus p d ∧
            (omega4 * (16 : ℝ) ^ (-4 : ℤ) < θ → collinearQuadsTorus p d θ = ∅) ∧
            BallLiftsAgree p d θ ∧ PeriodizationAgrees p d θ ∧
            (θ ≤ collinearThetaBound → (collinearQuadsTorus p d θ).Nonempty)
end Collinear
end QuadrupleClasses
end YangMills.Construction
end
