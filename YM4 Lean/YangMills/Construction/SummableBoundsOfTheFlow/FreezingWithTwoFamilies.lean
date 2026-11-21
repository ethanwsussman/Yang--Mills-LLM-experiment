import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison
namespace TorusFreezing
def ExpectationDecouples (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (l : StepLaw) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (α : ℝ) (A : StepVariable (finiteCells F) → ℝ) (A' : StepVariable (finiteCells F') → ℝ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    l.IsAdmissible T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' → 0 ≤ α →
    ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < T.ballRadius} →
    ContDiffOn ℝ 1 A' {η | ∀ b, ‖η b‖ < T.ballRadius} →
    ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ α T.p T.blockIndex q Y Y' j j'
      (l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V) A
      (l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V') A' →
    |ballExpectation (cutoffFactor T.ballRadius T.p)
        (l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V) A -
        ballExpectation (cutoffFactor T.ballRadius T.p)
          (l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V') A'| ≤
      T.Cs * l.amplitude T.energyRatio ^ 2 * α * Real.exp (-(T.κ * q / 2 ^ 7))
def expectationDecouples : Prop := EventuallyInParameters ExpectationDecouples
end TorusFreezing
end YangMills.Construction
end
