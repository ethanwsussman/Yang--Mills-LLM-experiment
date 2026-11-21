import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace TorusFreezing
def RemainderIsAdmissible (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s τ : ℝ) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 ≤ τ → τ ≤ 1 → IsCubicTopTorus T.L t T.n₀ F →
    IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q →
    TorusComparison.IsShortPairing Y Y' q j j' →
    (TorusComparison.ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ T.Cs T.p T.blockIndex
      q Y Y' j j'
      (Interpolation.weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)
      (TorusComparison.cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x
        (frameRadius x) Y V)
      (Interpolation.weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V')
      (TorusComparison.cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x
        (frameRadius x) Y' V')) ∧
    ContDiffOn ℝ 1 (TorusComparison.cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x
      (frameRadius x) Y V) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
    ContDiffOn ℝ 1 (TorusComparison.cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x
      (frameRadius x) Y' V') {η | ∀ b, ‖η b‖ < T.ballRadius}
def remainderIsAdmissible : Prop := EventuallyInParameters RemainderIsAdmissible
end TorusFreezing
end YangMills.Construction
end
