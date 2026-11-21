import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import YangMills.Construction.Torus.IntegralsAndLiftsToABall
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SingleBallPairs
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.TestPairs
def IntegralWithinBounds (d ϑ s i : ℝ) : Prop :=
  ϑ * s * d ^ 4 ≤ i ∧ i ≤ Real.pi ^ 2 / 2 * s * d ^ 4
def SupportsWithin {Y : Type*} [TopologicalSpace Y] (A : Set Y) (f g : Y → ℝ) : Prop :=
  tsupport f ⊆ A ∧ tsupport g ⊆ A
def EuclidPairProperties (d ϑ : ℝ) (p q : Fin 4 → ℝ) (f g : (Fin 4 → ℝ) → ℝ) : Prop :=
  euclidDistR4 p q ≤ 8 * d ∧
    SupportsWithin (closedBallR4 (midpointR4 p q) (5 * d)) f g ∧
    SupportsSeparated euclidDistR4 d f g ∧
    IntegralWithinBounds d ϑ (uniformNorm f) (∫ x, f x) ∧
    IntegralWithinBounds d ϑ (uniformNorm g) (∫ x, g x) ∧
    IsKernelPairR4 f g ∧
    KernelBoundChain d ϑ (uniformNorm f) (uniformNorm g) (∫ x, f x) (∫ x, g x)
      (inverseEighthKernel f g)
def TorusKernelWellDefined {ℓ : ℝ} (f g : Torus4 ℓ → ℝ) : Prop :=
  (∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f g q.1 q.2) ∧
    ∀ (c : Fin 4 → ℝ) (r : ℝ), IsKernelBallTorus f g c r →
      IsKernelPairR4 (liftToBall ℓ c r f) (liftToBall ℓ c r g) ∧
        inverseEighthKernel (liftToBall ℓ c r f) (liftToBall ℓ c r g) =
          inverseEighthKernelTorus f g
def TorusPairProperties {ℓ : ℝ} (d ϑ : ℝ) (p q : Torus4 ℓ) (f g : Torus4 ℓ → ℝ) : Prop :=
  euclidDistTorus p q ≤ 8 * d ∧
    (∃ y, SupportsWithin (closedBallTorus y (5 * d)) f g) ∧
    SupportsSeparated euclidDistTorus d f g ∧
    IntegralWithinBounds d ϑ (uniformNorm f) (torusVolumeIntegral ℓ f) ∧
    IntegralWithinBounds d ϑ (uniformNorm g) (torusVolumeIntegral ℓ g) ∧
    TorusKernelWellDefined f g ∧
    KernelBoundChain d ϑ (uniformNorm f) (uniformNorm g) (torusVolumeIntegral ℓ f)
      (torusVolumeIntegral ℓ g) (inverseEighthKernelTorus f g)
def BallLiftProperties (ℓ d ϑ : ℝ) (c P Q : Fin 4 → ℝ) (f g : Torus4 ℓ → ℝ) : Prop :=
  torusProj ℓ '' closedBallR4 c (5 * d) = closedBallTorus (torusProj ℓ c) (5 * d) ∧
    SupportsWithin (torusProj ℓ '' closedBallR4 c (5 * d)) f g ∧
    IsSupportedInBallImage ℓ c (5 * d) (fun u => (f u : ℂ)) ∧
    IsSupportedInBallImage ℓ c (5 * d) (fun u => (g u : ℂ)) ∧
    (liftToBall ℓ c (5 * d) f, liftToBall ℓ c (5 * d) g) ∈ separatedPairsR4 d ϑ ∧
    IsCentrePairR4 d ϑ P Q (liftToBall ℓ c (5 * d) f, liftToBall ℓ c (5 * d) g) ∧
    IsPeriodizable ℓ (closedBallR4 c (5 * d)) (liftToBall ℓ c (5 * d) f) ∧
    IsPeriodizable ℓ (closedBallR4 c (5 * d)) (liftToBall ℓ c (5 * d) g) ∧
    periodize ℓ (liftToBall ℓ c (5 * d) f) = f ∧ periodize ℓ (liftToBall ℓ c (5 * d) g) = g
def IsIsometricLiftPair {ℓ : ℝ} (p q : Torus4 ℓ) (P Q : Fin 4 → ℝ) : Prop :=
  IsLiftOfTorusPoint ℓ p P ∧ IsLiftOfTorusPoint ℓ q Q ∧ euclidDistR4 P Q = euclidDistTorus p q
def MainStatement : Prop :=
  (∀ d ϑ : ℝ, IsSepShapePair d ϑ →
    ∀ (p q : Fin 4 → ℝ) (f g : (Fin 4 → ℝ) → ℝ), (f, g) ∈ separatedPairsR4 d ϑ →
      IsCentrePairR4 d ϑ p q (f, g) → EuclidPairProperties d ϑ p q f g) ∧
  ∀ (L : ℕ) (ℓ d ϑ : ℝ), IsSepShapePair d ϑ → IsAdmissibleSide L ℓ d →
    ∀ (p q : Torus4 ℓ) (f g : Torus4 ℓ → ℝ), (f, g) ∈ separatedPairsTorus ℓ d ϑ →
      IsCentrePairTorus ℓ d ϑ p q (f, g) →
        TorusPairProperties d ϑ p q f g ∧
          (∃ P Q : Fin 4 → ℝ, IsIsometricLiftPair p q P Q) ∧
          ∀ P Q : Fin 4 → ℝ, IsIsometricLiftPair p q P Q →
            BallLiftProperties ℓ d ϑ (midpointR4 P Q) P Q f g
end YangMills.Construction.SingleBallPairs
