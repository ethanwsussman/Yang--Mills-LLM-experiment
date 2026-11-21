import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheMeansOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ThirdDerivLocalForParameters (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star,
      ThirdDerivCovarianceLocal star T.a T.chainParams.ρA T.ballRadius x T.κ T.E T.energyRatio T.Cs
        (frameRadius x) T.p f V
def ThirdDerivLocalEventually : Prop := EventuallyInParameters ThirdDerivLocalForParameters
end YangMills.Construction.ColdStepAtMirrorFrames
end
