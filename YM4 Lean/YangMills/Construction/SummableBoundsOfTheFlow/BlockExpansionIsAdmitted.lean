import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms
namespace TorusComparison
def InterpolatedBlockExpansionAdmissibleAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s ε : ℝ) (φ h : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 < ε →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' →
    (ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ (T.Cs * ε / T.η₃) T.p T.blockIndex q Y Y' j j'
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
      (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y η V)
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V')
      (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y' η V')) ∧
    ContDiffOn ℝ 1 (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y η V)
      {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
    ContDiffOn ℝ 1 (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y' η V')
      {η | ∀ b, ‖η b‖ < T.ballRadius}
def interpolatedBlockExpansionAdmissibleStatement : Prop := EventuallyInParameters InterpolatedBlockExpansionAdmissibleAt
end TorusComparison
end YangMills.Construction
end
