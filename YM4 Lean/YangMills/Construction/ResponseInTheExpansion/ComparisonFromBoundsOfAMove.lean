import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusComparison
variable {F : BlockFrame}
structure IsVanishingMoveWithGradient (ρ x κ g₀ g₁ : ℝ) (Y : F.Cell) (A : StepVariable (finiteCells F) → ℝ) :
    Prop where
  smooth : ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ}
  bounded : ∃ M : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |A η| ≤ M
  map_zero : A 0 = 0
  gradient_le : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b : ↥(chordBonds (finiteCells F)),
    bondGradNorm A b η ≤ (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y η))) *
      Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b))
def ComparisonFromGradientBoundsAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell)
    (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) (g₀ g₁ α : ℝ) (A : StepVariable (finiteCells F) → ℝ)
    (A' : StepVariable (finiteCells F') → ℝ), IsAdmissibleAt T t x f F V → IsAdmissibleAt T t x f F' V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' → 0 ≤ g₀ → 0 ≤ g₁ →
    C * (g₀ * x ^ (-(1 / 2) : ℝ) + g₁) ≤ α →
    IsVanishingMoveWithGradient T.ballRadius x T.κ g₀ g₁ Y A →
    IsVanishingMoveWithGradient T.ballRadius x T.κ g₀ g₁ Y' A' →
    (T.blockIndex ≤ q → ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < T.ballRadius) →
      |A (toTorus j ζ) - A' (toTorus j' ζ)| ≤ Real.exp (-(4 * T.κ * q)) *
        (g₀ * ∑ i, Real.exp (-(T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ +
          g₁ * (x * ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2 + 1))) →
    ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ α T.p T.blockIndex q Y Y' j j'
      ((coldHalfLawAt T x f).exponent V) A ((coldHalfLawAt T x f).exponent V') A'
def comparisonFromGradientBoundsStatement : Prop :=
  ∃ C : StepParameters → ℝ, (∀ T, 0 ≤ C T) ∧
    EventuallyInParameters fun T => ComparisonFromGradientBoundsAt T (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
