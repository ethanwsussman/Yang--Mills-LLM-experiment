import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Torus.LiftOfASeparatedTestPair
import YangMills.Construction.Torus.TestPairsCentresAndTorusLebesgueMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
namespace PairTransport
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
abbrev periodizeOnTorus (L m : ℕ) (f : (Fin 4 → ℝ) → ℝ) : FourTorus L m → ℝ :=
  periodize (torusSide L m) f
def KernelTwoSidedBound (θ A B K : ℝ) : Prop :=
  (10 : ℝ) ^ (-8 : ℤ) * θ ^ 2 * A * B ≤ K ∧ K ≤ Real.pi ^ 4 / 4 * A * B
def PairGeometryR4 (d θ : ℝ) (a₁ a₂ : Fin 4 → ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ) : Prop :=
  0 < uniformNorm φ ∧ 0 < uniformNorm ψ ∧ euclidDistR4 a₁ a₂ ≤ 8 * d ∧
    tsupport φ ⊆ closedBallR4 ((1 / 2 : ℝ) • (a₁ + a₂)) (5 * d) ∧
    tsupport ψ ⊆ closedBallR4 ((1 / 2 : ℝ) • (a₁ + a₂)) (5 * d) ∧
    (∀ u ∈ tsupport φ, ∀ v ∈ tsupport ψ, d ≤ euclidDistR4 u v ∧ euclidDistR4 u v ≤ 10 * d) ∧
    KernelTwoSidedBound θ (uniformNorm φ) (uniformNorm ψ) (inverseEighthKernel φ ψ)
def KernelTorusWellDefined {ℓ : ℝ} (φ ψ : Torus4 ℓ → ℝ) : Prop :=
  (∃ (c : Fin 4 → ℝ) (r : ℝ), IsKernelBallTorus φ ψ c r) ∧
    ∀ (c : Fin 4 → ℝ) (r : ℝ), IsKernelBallTorus φ ψ c r →
      IsKernelPairR4 (liftToBall ℓ c r φ) (liftToBall ℓ c r ψ) ∧
        inverseEighthKernel (liftToBall ℓ c r φ) (liftToBall ℓ c r ψ) = inverseEighthKernelTorus φ ψ
def PeriodizationOfPairR4 (L m : ℕ) (d θ : ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ) : Prop :=
  (periodizeOnTorus L m φ, periodizeOnTorus L m ψ) ∈ separatedPairsFourTorus L m d θ ∧
    uniformNorm (periodizeOnTorus L m φ) = uniformNorm φ ∧
    uniformNorm (periodizeOnTorus L m ψ) = uniformNorm ψ ∧
    KernelTorusWellDefined (periodizeOnTorus L m φ) (periodizeOnTorus L m ψ) ∧
    inverseEighthKernelTorus (periodizeOnTorus L m φ) (periodizeOnTorus L m ψ) =
      inverseEighthKernel φ ψ ∧
    IsPairLift d θ (periodizeOnTorus L m φ) (periodizeOnTorus L m ψ) φ ψ
def PairLiftProperties (d θ : ℝ) (φ ψ : FourTorus L m → ℝ) (φ' ψ' : (Fin 4 → ℝ) → ℝ) : Prop :=
  (φ', ψ') ∈ separatedPairsR4 d θ ∧ periodizeOnTorus L m φ' = φ ∧ periodizeOnTorus L m ψ' = ψ ∧
    uniformNorm φ' = uniformNorm φ ∧ uniformNorm ψ' = uniformNorm ψ ∧
    inverseEighthKernel φ' ψ' = inverseEighthKernelTorus φ ψ
def PairTorusProperties (d θ : ℝ) (φ ψ : FourTorus L m → ℝ) : Prop :=
  (∃ z : FourTorus L m, SupportsInBall z (9 * d) ![φ, ψ]) ∧
    (∃ φ' ψ', IsPairLift d θ φ ψ φ' ψ') ∧
    (∀ φ' ψ', IsPairLift d θ φ ψ φ' ψ' → PairLiftProperties d θ φ ψ φ' ψ') ∧
    KernelTwoSidedBound θ (uniformNorm φ) (uniformNorm ψ) (inverseEighthKernelTorus φ ψ) ∧
    ∀ φ₁ ψ₁ φ₂ ψ₂, IsPairLift d θ φ ψ φ₁ ψ₁ → IsPairLift d θ φ ψ φ₂ ψ₂ →
      ∃ k : Fin 4 → ℤ, (φ₂ = fun y => φ₁ (y - latticeTranslate (torusSide L m) k)) ∧
        ψ₂ = fun y => ψ₁ (y - latticeTranslate (torusSide L m) k)
def LiftsPeriodizeConsistently (n : ℕ) (d θ : ℝ) (φ ψ : FourTorus L m → ℝ) : Prop :=
  (∀ φ₁ ψ₁ φ₂ ψ₂, IsPairLift d θ φ ψ φ₁ ψ₁ → IsPairLift d θ φ ψ φ₂ ψ₂ →
      periodizeOnTorus L n φ₁ = periodizeOnTorus L n φ₂ ∧
        periodizeOnTorus L n ψ₁ = periodizeOnTorus L n ψ₂) ∧
    ∀ φ' ψ', IsPairLift d θ φ ψ φ' ψ' →
      (periodizeOnTorus L n φ', periodizeOnTorus L n ψ') ∈ separatedPairsFourTorus L n d θ ∧
        uniformNorm (periodizeOnTorus L n φ') = uniformNorm φ ∧
        uniformNorm (periodizeOnTorus L n ψ') = uniformNorm ψ ∧
        inverseEighthKernelTorus (periodizeOnTorus L n φ') (periodizeOnTorus L n ψ') =
          inverseEighthKernelTorus φ ψ
def DilationPairR4 (L b : ℕ) (d θ : ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ) : Prop :=
  (dilateR4 L b φ, dilateR4 L b ψ) ∈ separatedPairsR4 ((L : ℝ) ^ b * d) θ ∧
    uniformNorm (dilateR4 L b φ) = uniformNorm φ ∧ uniformNorm (dilateR4 L b ψ) = uniformNorm ψ ∧
    inverseEighthKernel (dilateR4 L b φ) (dilateR4 L b ψ) = inverseEighthKernel φ ψ
def DilationPairTorus (b : ℕ) (d θ : ℝ) (φ ψ : FourTorus L m → ℝ) : Prop :=
  torusSide L (m + b) = (L : ℝ) ^ b * torusSide L m ∧ (L : ℝ) ^ b * torusSide L m ∈ torusSides L ∧
    40 * ((L : ℝ) ^ b * d) ≤ (L : ℝ) ^ b * torusSide L m ∧
    (dilateTorus L m b φ, dilateTorus L m b ψ) ∈
      separatedPairsFourTorus L (m + b) ((L : ℝ) ^ b * d) θ ∧
    uniformNorm (dilateTorus L m b φ) = uniformNorm φ ∧
    uniformNorm (dilateTorus L m b ψ) = uniformNorm ψ ∧
    inverseEighthKernelTorus (dilateTorus L m b φ) (dilateTorus L m b ψ) =
      inverseEighthKernelTorus φ ψ
def PairTransportStatement : Prop :=
  ∀ (s : Conventions.StandingParameters) (d θ : ℝ), IsSepShapePair d θ →
    (∀ (φ ψ : (Fin 4 → ℝ) → ℝ) (a₁ a₂ : Fin 4 → ℝ), (φ, ψ) ∈ separatedPairsR4 d θ →
      IsCentrePairR4 d θ a₁ a₂ (φ, ψ) → PairGeometryR4 d θ a₁ a₂ φ ψ) ∧
    (40 * d ≤ s.side → ∀ φ ψ : (Fin 4 → ℝ) → ℝ, (φ, ψ) ∈ separatedPairsR4 d θ →
      PeriodizationOfPairR4 s.L s.m d θ φ ψ) ∧
    (40 * d ≤ s.side → ∀ φ ψ : s.Torus → ℝ, (φ, ψ) ∈ separatedPairsFourTorus s.L s.m d θ →
      PairTorusProperties d θ φ ψ) ∧
    (∀ n : ℕ, torusSide s.L n ∈ torusSides s.L → 40 * d ≤ torusSide s.L n →
      torusSide s.L n ≤ s.side →
      ∀ φ ψ : s.Torus → ℝ, (φ, ψ) ∈ separatedPairsFourTorus s.L s.m d θ →
        LiftsPeriodizeConsistently n d θ φ ψ) ∧
    ∀ b : ℕ,
      (∀ φ ψ : (Fin 4 → ℝ) → ℝ, (φ, ψ) ∈ separatedPairsR4 d θ →
        DilationPairR4 s.L b d θ φ ψ) ∧
      (40 * d ≤ s.side → ∀ φ ψ : s.Torus → ℝ, (φ, ψ) ∈ separatedPairsFourTorus s.L s.m d θ →
        DilationPairTorus b d θ φ ψ)
end PairTransport
end TestFunctions
end YangMills.Construction
end
