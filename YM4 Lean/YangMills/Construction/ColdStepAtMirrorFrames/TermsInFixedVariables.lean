import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
def ExponentsConvexAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool) (ν : ℝ),
    T.coupling ≤ x → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ ν → ν ≤ 1 →
    StepExponentIsConvex star T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ (frameRadius x) f ν V
def exponentConvexityStatement : Prop := EventuallyInParameters ExponentsConvexAt
end ColdStepAtMirrorFrames
end YangMills.Construction
end
