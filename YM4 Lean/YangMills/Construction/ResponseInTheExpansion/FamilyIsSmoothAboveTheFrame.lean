import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace LinearResponse
variable {F : BlockFrame}
def CentredExpansionContDiffAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool), T.coupling ≤ x →
    IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
def CentredExpansionContDiff : Prop := EventuallyInParameters CentredExpansionContDiffAt
end LinearResponse
end YangMills.Construction
end
