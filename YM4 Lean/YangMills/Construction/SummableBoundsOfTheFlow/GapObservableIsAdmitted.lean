import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison FamilyNorms
namespace TorusFreezing
def GapObservableIsAdmissible (T : StepParameters) : Prop :=
  ∀ N : ℕ, ∃ CN : ℝ, ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F F' : BlockFrame)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' →
    4 * frameRadius x < q →
    (ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ (CN * (x ^ N)⁻¹) T.p T.blockIndex q Y Y' j j'
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
      (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V')
      (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y' V')) ∧
    ContDiffOn ℝ 1 (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
      {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
    ContDiffOn ℝ 1 (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y' V')
      {η | ∀ b, ‖η b‖ < T.ballRadius}
def gapObservableIsAdmissible : Prop := EventuallyInParameters GapObservableIsAdmissible
end TorusFreezing
end YangMills.Construction
end
