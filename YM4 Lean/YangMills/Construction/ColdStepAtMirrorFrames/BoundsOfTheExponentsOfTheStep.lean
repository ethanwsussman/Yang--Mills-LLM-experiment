import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CellExponentsBoundedAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool), T.coupling ≤ x →
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    CellExponentBounds star T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V ∧
    ∀ (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y
          (leftTranslate (bondSpread c X q.1) V) q.2) (0, η)
def CellExponentsBounded : Prop := EventuallyInParameters CellExponentsBoundedAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
