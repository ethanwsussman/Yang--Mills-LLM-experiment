import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms
namespace TorusFreezing
def BlockExpansionExpectationDecouples (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s ε : ℝ) (φ h : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 < ε →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q →
    |ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
        (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y η V) -
      ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V')
        (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y' η V')| ≤
      T.CE * ε * Real.exp (-(T.κ * q / 2 ^ 7))
def blockExpansionExpectationDecouples : Prop := EventuallyInParameters BlockExpansionExpectationDecouples
end TorusFreezing
end YangMills.Construction
end
