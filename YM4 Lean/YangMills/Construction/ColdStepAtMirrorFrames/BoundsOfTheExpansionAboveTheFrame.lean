import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CentredExpansionsBoundedAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    CentredExpansionBounds star T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V
def CentredExpansionsBounded : Prop := EventuallyInParameters CentredExpansionsBoundedAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
