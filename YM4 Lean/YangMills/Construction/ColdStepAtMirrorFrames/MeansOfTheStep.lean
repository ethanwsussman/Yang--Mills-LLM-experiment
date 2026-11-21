import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheMeansOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CovarianceBoundsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star,
      ThirdDerivCovarianceLocal star T.a T.chainParams.ρA T.ballRadius x T.κ T.E T.energyRatio T.Cs
        (frameRadius x) T.p f V ∧
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        MeansLocalize star T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.CE
          (frameRadius x) T.p f V V' Y Y' r
def covarianceBoundsStatement : Prop := EventuallyInParameters CovarianceBoundsAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
