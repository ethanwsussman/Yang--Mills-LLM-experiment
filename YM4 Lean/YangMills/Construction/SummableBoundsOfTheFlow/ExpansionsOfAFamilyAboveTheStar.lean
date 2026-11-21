import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def CentredExpansionContDiff (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x ε ε₃ : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)),
    P.coupling ≤ x → 0 ≤ ε → 0 ≤ ε₃ → FamilyNorms.IsNormBoundedLocalFamily P.L t P.n₀ P.σ P.decayRate ε ε₃ f →
    IsCubicTopTorus P.L t P.n₀ F →
    IsSmallCurvature (5 / 4 * P.σ) V → (∀ b, ‖η b‖ ≤ P.ballRadius) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      centredExpansion true P.a P.chainParams.ρA (frameRadius x) f y q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
def centredExpansionContDiffStatement : Prop := EventuallyInParameters CentredExpansionContDiff
end YangMills.Construction.BlockMeans
end
