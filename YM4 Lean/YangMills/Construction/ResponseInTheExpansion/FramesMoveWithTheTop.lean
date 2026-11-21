import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
def FramesEquivariantAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    (∀ (γ : F.Cell → UnitQuaternion), ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V) =
        adjointAction (γ (enclosingCell b.1)) (stepFrame false T.a T.chainParams.ρA (frameRadius x) b V)) ∧
    (∀ (h : F.Cell), ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false T.a T.chainParams.ρA (frameRadius x) (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false T.a T.chainParams.ρA (frameRadius x) b V) ∧
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature (3 / 4 * T.σ) (fieldAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η) ∧
      IsAdmissibleChartPoint T.L T.chainParams.σA
        (coordsAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η) V
def framesEquivariantStatement : Prop := EventuallyInParameters FramesEquivariantAt
end ResponseInTheExpansion
end YangMills.Construction
end
