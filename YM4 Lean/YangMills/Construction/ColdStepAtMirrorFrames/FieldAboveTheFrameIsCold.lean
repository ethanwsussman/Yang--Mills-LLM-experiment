import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def FieldAboveFrameSmallCurvatureAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η)
def fieldAboveFrameSmallCurvature : Prop := EventuallyInParameters FieldAboveFrameSmallCurvatureAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
