import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.FamilyNorms
namespace YangMills.Construction.Interpolation
def familyLawExponentSmoothAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × StepVariable (finiteCells F)) =>
      familyLawExponent q.2.1 T.a T.chainParams.ρA x (frameRadius x) φ
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2.2) (0, s, η)
def FamilyLawExponentSmooth : Prop := EventuallyInParameters familyLawExponentSmoothAt
end YangMills.Construction.Interpolation
end
