import YangMills.Construction.Torus.IntegralsAndLiftsToABall
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
namespace SmallBalls
open YangMills.Construction.TorusMetric
def ProjDistFormula (ℓ : ℝ) : Prop :=
  ∀ a b : Fin 4 → ℝ,
    IsLeast (range fun n : Fin 4 → ℤ => euclidNormVec (a - b - latticeTranslate ℓ n))
        (euclidDistTorus (torusProj ℓ a) (torusProj ℓ b)) ∧
      euclidDistTorus (torusProj ℓ a) (torusProj ℓ b) ≤ euclidNormVec (a - b) ∧
      (euclidNormVec (a - b) ≤ ℓ / 2 →
        euclidDistTorus (torusProj ℓ a) (torusProj ℓ b) = euclidNormVec (a - b))
def ExistsNearestLift (ℓ : ℝ) : Prop :=
  ∀ (p q : Torus4 ℓ) (a : Fin 4 → ℝ), IsLiftOfTorusPoint ℓ p a →
    ∃ b, IsLiftOfTorusPoint ℓ q b ∧ euclidNormVec (a - b) = euclidDistTorus p q
def DistTriangle (ℓ : ℝ) : Prop :=
  ∀ p q r : Torus4 ℓ, euclidDistTorus p r ≤ euclidDistTorus p q + euclidDistTorus q r
def BallMapsOntoBall (ℓ : ℝ) (c : Fin 4 → ℝ) (ρ : ℝ) : Prop :=
  BijOn (torusProj ℓ) (closedBallR4 c ρ) (closedBallTorus (torusProj ℓ c) ρ) ∧
    ∀ a ∈ closedBallR4 c ρ, ∀ b ∈ closedBallR4 c ρ,
      euclidDistTorus (torusProj ℓ a) (torusProj ℓ b) = euclidNormVec (a - b)
def vanishOffBall (c : Fin 4 → ℝ) (ρ : ℝ) : Set ((Fin 4 → ℝ) → ℂ) :=
  {f | ∀ a, a ∉ closedBallR4 c ρ → f a = 0}
def vanishOffImage (ℓ : ℝ) (c : Fin 4 → ℝ) (ρ : ℝ) : Set (Torus4 ℓ → ℂ) :=
  {F | ∀ p, p ∉ torusProj ℓ '' closedBallR4 c ρ → F p = 0}
def PeriodizeOnBall (ℓ : ℝ) (c : Fin 4 → ℝ) (ρ : ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  IsPeriodizable ℓ (closedBallR4 c ρ) f ∧
    (∀ a ∈ closedBallR4 c ρ, periodize ℓ f (torusProj ℓ a) = f a) ∧
    ∀ p, p ∉ torusProj ℓ '' closedBallR4 c ρ → periodize ℓ f p = 0
def PeriodizeBijective (ℓ : ℝ) (c : Fin 4 → ℝ) (ρ : ℝ) : Prop :=
  BijOn (periodize ℓ) (vanishOffBall c ρ) (vanishOffImage ℓ c ρ) ∧
    InvOn (liftToBall ℓ c ρ) (periodize ℓ) (vanishOffBall c ρ) (vanishOffImage ℓ c ρ)
def PeriodizeValues (ℓ : ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  range (periodize ℓ f) = range f ∧
    (IsBoundedFun f → uniformNorm (periodize ℓ f) = uniformNorm f) ∧
    ((∀ p, 0 ≤ periodize ℓ f p) ↔ ∀ a, 0 ≤ f a) ∧
    (periodize ℓ f ≠ 0 ↔ f ≠ 0)
def PeriodizeSupport (ℓ : ℝ) (c : Fin 4 → ℝ) (ρ : ℝ) (f g : (Fin 4 → ℝ) → ℂ) : Prop :=
  tsupport f ⊆ closedBallR4 c ρ ∧
    tsupport (periodize ℓ f) = torusProj ℓ '' tsupport f ∧
    setEuclidDist (tsupport (periodize ℓ f)) (tsupport (periodize ℓ g)) =
      setDistR4 (tsupport f) (tsupport g)
def PeriodizeLipschitz (ℓ : ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  (IsLipschitzFor euclidDistR4 f ↔ IsLipschitzFor (euclidDistTorus (ℓ := ℓ)) (periodize ℓ f)) ∧
    (IsLipschitzFor euclidDistR4 f → lipConstTorus (periodize ℓ f) = lipConstR4 f)
def PeriodizeIntegral (ℓ : ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  IsBoundedFun f → Measurable f →
    IsBoundedFun (periodize ℓ f ∘ torusProj ℓ) ∧ Measurable (periodize ℓ f ∘ torusProj ℓ) ∧
      torusIntegralComplex ℓ (periodize ℓ f) = ∫ a, f a
def SupportsInSmallBall {ℓ : ℝ} (F G : Torus4 ℓ → ℂ) : Prop :=
  0 < setEuclidDist (tsupport F) (tsupport G) ∧
    ∃ (p : Torus4 ℓ) (r : ℝ), 0 < r ∧ r ≤ ℓ / 8 ∧
      tsupport F ⊆ closedBallTorus p r ∧ tsupport G ⊆ closedBallTorus p r
def BallCoversSupports {ℓ : ℝ} (F G : Torus4 ℓ → ℂ) (c : Fin 4 → ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ ℓ / 4 ∧ tsupport F ⊆ torusProj ℓ '' closedBallR4 c ρ ∧
    tsupport G ⊆ torusProj ℓ '' closedBallR4 c ρ
def LiftsAgree {ℓ : ℝ} (F G : Torus4 ℓ → ℂ) (c₁ : Fin 4 → ℝ) (ρ₁ : ℝ)
    (c₂ : Fin 4 → ℝ) (ρ₂ : ℝ) : Prop :=
  IsKernelPairR4 (liftToBall ℓ c₁ ρ₁ F) (liftToBall ℓ c₁ ρ₁ G) ∧
    IsKernelPairR4 (liftToBall ℓ c₂ ρ₂ F) (liftToBall ℓ c₂ ρ₂ G) ∧
    (∃ n : Fin 4 → ℤ,
      liftToBall ℓ c₂ ρ₂ F = (fun a => liftToBall ℓ c₁ ρ₁ F (a - latticeTranslate ℓ n)) ∧
        liftToBall ℓ c₂ ρ₂ G = fun a => liftToBall ℓ c₁ ρ₁ G (a - latticeTranslate ℓ n)) ∧
    inverseEighthKernel (liftToBall ℓ c₂ ρ₂ F) (liftToBall ℓ c₂ ρ₂ G) =
      inverseEighthKernel (liftToBall ℓ c₁ ρ₁ F) (liftToBall ℓ c₁ ρ₁ G)
def KernelIndependentOfBall (ℓ : ℝ) : Prop :=
  ∀ F G : Torus4 ℓ → ℂ, IsBoundedMeasurableOnTorus F → IsBoundedMeasurableOnTorus G →
    SupportsInSmallBall F G →
      (∀ (c₁ : Fin 4 → ℝ) (ρ₁ : ℝ) (c₂ : Fin 4 → ℝ) (ρ₂ : ℝ),
        BallCoversSupports F G c₁ ρ₁ → BallCoversSupports F G c₂ ρ₂ →
          LiftsAgree F G c₁ ρ₁ c₂ ρ₂) ∧
      ∀ (c : Fin 4 → ℝ) (r : ℝ), IsKernelBallTorus F G c r →
        inverseEighthKernelTorus F G = inverseEighthKernel (liftToBall ℓ c r F) (liftToBall ℓ c r G)
def CoveringOnSmallBalls : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ →
    ProjDistFormula ℓ ∧ ExistsNearestLift ℓ ∧ DistTriangle ℓ ∧
      (∀ (c : Fin 4 → ℝ) (ρ : ℝ), 0 < ρ → ρ ≤ ℓ / 4 →
        BallMapsOntoBall ℓ c ρ ∧
          (∀ f ∈ vanishOffBall c ρ, PeriodizeOnBall ℓ c ρ f) ∧
          PeriodizeBijective ℓ c ρ ∧
          ∀ f ∈ vanishOffBall c ρ, ∀ g ∈ vanishOffBall c ρ,
            PeriodizeValues ℓ f ∧ PeriodizeSupport ℓ c ρ f g ∧ PeriodizeLipschitz ℓ f ∧
              PeriodizeIntegral ℓ f) ∧
      KernelIndependentOfBall ℓ
end SmallBalls
end TestFunctions
end YangMills.Construction
end
