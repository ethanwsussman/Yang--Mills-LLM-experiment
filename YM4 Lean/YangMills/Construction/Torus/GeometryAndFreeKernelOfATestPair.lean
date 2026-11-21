import YangMills.Construction.Torus.TestPairsCentresAndTorusLebesgueMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set TorusMetric PeriodicLattice TestFunctions
open scoped ENNReal
namespace TestPairs
def kernelLowerConst : ℝ := 10 ^ (-8 : ℤ)
def kernelUpperConst : ℝ := (Real.pi ^ 2 / 2) ^ 2
def KernelBoundChain (d θ a₁ a₂ m₁ m₂ k : ℝ) : Prop :=
  kernelLowerConst * θ ^ 2 * a₁ * a₂ ≤ (10 * d) ^ (-8 : ℤ) * m₁ * m₂ ∧
    (10 * d) ^ (-8 : ℤ) * m₁ * m₂ ≤ k ∧ k ≤ d ^ (-8 : ℤ) * m₁ * m₂ ∧
    d ^ (-8 : ℤ) * m₁ * m₂ ≤ kernelUpperConst * a₁ * a₂
section Geometry
variable {X : Type*} [TopologicalSpace X]
def ContainsPair (B : X → ℝ → Set X) (d : ℝ) (p₁ p₂ : X) (S : Set X) (g₁ g₂ : X → ℝ) : Prop :=
  B p₁ d ∪ B p₂ d ⊆ S ∧ tsupport g₁ ∪ tsupport g₂ ⊆ S
def SupportsSeparated (δ : X → X → ℝ) (d : ℝ) (g₁ g₂ : X → ℝ) : Prop :=
  ∀ a ∈ tsupport g₁, ∀ b ∈ tsupport g₂, d ≤ δ a b ∧ δ a b ≤ 10 * d
end Geometry
def midpointR4 (P₁ P₂ : Fin 4 → ℝ) : Fin 4 → ℝ := (1 / 2 : ℝ) • (P₁ + P₂)
def PairBoundsR4 (d θ : ℝ) (p₁ p₂ : Fin 4 → ℝ) (g₁ g₂ : (Fin 4 → ℝ) → ℝ) : Prop :=
  euclidDistR4 p₁ p₂ ≤ 8 * d ∧
    ContainsPair closedBallR4 d p₁ p₂ (closedBallR4 (midpointR4 p₁ p₂) (5 * d)) g₁ g₂ ∧
    SupportsSeparated euclidDistR4 d g₁ g₂ ∧ IsKernelPairR4 g₁ g₂ ∧
    KernelBoundChain d θ (uniformNorm g₁) (uniformNorm g₂) (∫ x, g₁ x) (∫ x, g₂ x)
      (inverseEighthKernel g₁ g₂)
def PairBoundsTorus {ℓ : ℝ} (d θ : ℝ) (p₁ p₂ : Torus4 ℓ) (g₁ g₂ : Torus4 ℓ → ℝ) : Prop :=
  euclidDistTorus p₁ p₂ ≤ 8 * d ∧
    (∃ c, ContainsPair closedBallTorus d p₁ p₂ (closedBallTorus c (5 * d)) g₁ g₂) ∧
    SupportsSeparated euclidDistTorus d g₁ g₂ ∧
    (∃ r : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus g₁ g₂ r.1 r.2) ∧
    KernelBoundChain d θ (uniformNorm g₁) (uniformNorm g₂) (integralTorusLebesgue ℓ g₁)
      (integralTorusLebesgue ℓ g₂) (inverseEighthKernelTorus g₁ g₂)
def PreservesInvariants {ℓ : ℝ} (g₁ g₂ : Torus4 ℓ → ℝ) (h₁ h₂ : (Fin 4 → ℝ) → ℝ) : Prop :=
  uniformNorm h₁ = uniformNorm g₁ ∧ uniformNorm h₂ = uniformNorm g₂ ∧
    (∫ x, h₁ x) = integralTorusLebesgue ℓ g₁ ∧ (∫ x, h₂ x) = integralTorusLebesgue ℓ g₂ ∧
    lipConstR4 h₁ = lipConstTorus g₁ ∧ lipConstR4 h₂ = lipConstTorus g₂ ∧
    setDistR4 (tsupport h₁) (tsupport h₂) = setEuclidDist (tsupport g₁) (tsupport g₂) ∧
    inverseEighthKernel h₁ h₂ = inverseEighthKernelTorus g₁ g₂
def ProjIsometricOnto (ℓ : ℝ) (A : Set (Fin 4 → ℝ)) (S : Set (Torus4 ℓ)) : Prop :=
  torusProj ℓ '' A = S ∧
    ∀ a ∈ A, ∀ b ∈ A, euclidDistTorus (torusProj ℓ a) (torusProj ℓ b) = euclidDistR4 a b
def LiftProperties (ℓ d θ : ℝ) (p₁ p₂ : Torus4 ℓ) (P₁ P₂ : Fin 4 → ℝ)
    (g₁ g₂ : Torus4 ℓ → ℝ) : Prop :=
  5 * d ≤ ℓ / 8 ∧
    (∃ c, ProjIsometricOnto ℓ (closedBallR4 (midpointR4 P₁ P₂) (5 * d)) (closedBallTorus c (5 * d)) ∧
      ContainsPair closedBallTorus d p₁ p₂ (closedBallTorus c (5 * d)) g₁ g₂) ∧
    LiftsToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₁ ∧
    LiftsToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₂ ∧
    (liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₁,
      liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₂) ∈ separatedPairsR4 d θ ∧
    IsCentrePairR4 d θ P₁ P₂ (liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₁,
      liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₂) ∧
    PreservesInvariants g₁ g₂ (liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₁)
      (liftToBall ℓ (midpointR4 P₁ P₂) (5 * d) g₂)
def PeriodizationProperties (ℓ d θ : ℝ) (p₁ p₂ : Fin 4 → ℝ) (g₁ g₂ : (Fin 4 → ℝ) → ℝ) : Prop :=
  IsPeriodizable ℓ (closedBallR4 (midpointR4 p₁ p₂) (5 * d)) g₁ ∧
    IsPeriodizable ℓ (closedBallR4 (midpointR4 p₁ p₂) (5 * d)) g₂ ∧
    (periodize ℓ g₁, periodize ℓ g₂) ∈ separatedPairsTorus ℓ d θ ∧
    IsCentrePairTorus ℓ d θ (torusProj ℓ p₁) (torusProj ℓ p₂) (periodize ℓ g₁, periodize ℓ g₂) ∧
    LiftsToBall ℓ (midpointR4 p₁ p₂) (5 * d) (periodize ℓ g₁) ∧
    LiftsToBall ℓ (midpointR4 p₁ p₂) (5 * d) (periodize ℓ g₂) ∧
    liftToBall ℓ (midpointR4 p₁ p₂) (5 * d) (periodize ℓ g₁) = g₁ ∧
    liftToBall ℓ (midpointR4 p₁ p₂) (5 * d) (periodize ℓ g₂) = g₂ ∧
    PreservesInvariants (periodize ℓ g₁) (periodize ℓ g₂) g₁ g₂
def GeometryAndKernelBounds : Prop :=
  (∀ d θ : ℝ, IsSepShapePair d θ →
    ∀ (p₁ p₂ : Fin 4 → ℝ) (g₁ g₂ : (Fin 4 → ℝ) → ℝ), (g₁, g₂) ∈ separatedPairsR4 d θ →
      IsCentrePairR4 d θ p₁ p₂ (g₁, g₂) →
        PairBoundsR4 d θ p₁ p₂ g₁ g₂ ∧
          ∀ (N : ℕ) (ℓ' : ℝ), IsAdmissibleSide N ℓ' d →
            PeriodizationProperties ℓ' d θ p₁ p₂ g₁ g₂) ∧
  ∀ (N : ℕ) (ℓ d θ : ℝ), IsSepShapePair d θ → IsAdmissibleSide N ℓ d →
    ∀ (p₁ p₂ : Torus4 ℓ) (g₁ g₂ : Torus4 ℓ → ℝ), (g₁, g₂) ∈ separatedPairsTorus ℓ d θ →
      IsCentrePairTorus ℓ d θ p₁ p₂ (g₁, g₂) →
        PairBoundsTorus d θ p₁ p₂ g₁ g₂ ∧
          ∀ P₁ P₂ : Fin 4 → ℝ, torusProj ℓ P₁ = p₁ → torusProj ℓ P₂ = p₂ →
            euclidDistR4 P₁ P₂ = euclidDistTorus p₁ p₂ → LiftProperties ℓ d θ p₁ p₂ P₁ P₂ g₁ g₂
end TestPairs
end YangMills.Construction
