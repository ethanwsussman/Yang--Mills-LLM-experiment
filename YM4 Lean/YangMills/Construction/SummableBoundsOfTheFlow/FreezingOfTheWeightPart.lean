import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison
namespace TorusFreezing
def RemainderExpectationDecouples (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s τ : ℝ) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (q : ℕ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 ≤ τ → τ ≤ 1 →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q →
    |ballExpectation (cutoffFactor T.ballRadius T.p)
        (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)
        (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V) -
      ballExpectation (cutoffFactor T.ballRadius T.p)
        (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V')
        (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y' V')| ≤
      T.Cs * Real.exp (-(T.κ * q / 2 ^ 7))
def remainderExpectationDecouples : Prop := EventuallyInParameters RemainderExpectationDecouples
end TorusFreezing
end YangMills.Construction
end
