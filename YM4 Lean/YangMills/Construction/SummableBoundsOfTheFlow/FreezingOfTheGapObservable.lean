import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms
namespace TorusFreezing
def GapObservableExpectationDecouples (T : StepParameters) : Prop :=
  ∀ N : ℕ, ∃ CN : ℝ, ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → 4 * frameRadius x < q →
    |ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V) -
      ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V')
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y' V')| ≤
      CN * (x ^ N)⁻¹ * Real.exp (-(T.κ * q / 2 ^ 7))
def gapObservableExpectationDecouples : Prop := EventuallyInParameters GapObservableExpectationDecouples
end TorusFreezing
end YangMills.Construction
end
