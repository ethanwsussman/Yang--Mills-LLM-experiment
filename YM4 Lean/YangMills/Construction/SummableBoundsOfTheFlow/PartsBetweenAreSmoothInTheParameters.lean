import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
structure InterpolatedPartsSmooth (s a ρA ρ x : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  sum_eq : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    interpolatedExponent s a ρA x m V η = ∑ Y ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y V η
  smooth : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      interpolatedBlockExponent s a ρA x m Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2) (0, η)
  third_deriv : ∀ (Y : F.Cell) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ ρ) →
    ContDiffAt ℝ 4 (fun q : (Fin 3 → ℝ) × StepVariable (finiteCells F) =>
      interpolatedBlockExponent s a ρA x m Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2) (0, η)
def InterpolatedPartsSmoothAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), P.coupling ≤ x → IsCubicTopTorus P.L t P.n₀ F →
    IsSmallCurvature (5 / 4 * P.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedPartsSmooth s P.a P.chainParams.ρA P.ballRadius x (frameRadius x) V
def interpolatedPartsSmoothStatement : Prop := EventuallyInParameters InterpolatedPartsSmoothAt
end YangMills.Construction.Interpolation
end
