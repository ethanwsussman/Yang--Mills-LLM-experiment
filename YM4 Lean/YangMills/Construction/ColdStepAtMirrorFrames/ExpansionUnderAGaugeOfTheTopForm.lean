import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def imaginaryCoords (X : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(X : Quaternion ℝ).imI, (X : Quaternion ℝ).imJ, (X : Quaternion ℝ).imK]
def adjointStepVariable (γ : F.Cell → UnitQuaternion) (η : StepVariable (finiteCells F)) :
    StepVariable (finiteCells F) :=
  fun b => imaginaryCoords (adjointAction (γ (enclosingCell b.1.1)) (toImaginary (η b)))
def fieldOverFrameAt (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : F.GaugeField F.depth :=
  chartedField (fun x i => w (x, i) V + stepCoordinates η x i) V
def GaugeCovarianceOfFrame : Prop :=
  (∀ (F : BlockFrame) (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
      (γ : F.Cell → UnitQuaternion) (η : StepVariable (finiteCells F)), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
      (∀ b ∈ chordBonds (finiteCells F), w b (gaugeTransform γ V) = adjointAction (γ (enclosingCell b.1)) (w b V)) →
      fieldOverFrameAt w (gaugeTransform γ V) (adjointStepVariable γ η) =
        gaugeTransform (fun x => γ (enclosingCell x)) (fieldOverFrameAt w V η)) ∧
  (∀ (F : BlockFrame) (j k : ℕ) (G G' : F.GaugeField j → ℝ) (V : F.GaugeField j) (γ : F.Site j → UnitQuaternion)
      (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions),
      (∀ᶠ τ in nhds (0 : Fin k → ℝ), G' (gaugeTransform γ (leftTranslate (bondSpread c X τ) V)) =
        G (leftTranslate (bondSpread c X τ) V)) →
      bondDeriv G V c X = bondDeriv G' (gaugeTransform γ V) c fun l => adjointAction (γ (c l).1) (X l)) ∧
  ∀ (F : BlockFrame) (γ : F.Cell → UnitQuaternion) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))),
    ‖adjointStepVariable γ η b‖ = ‖η b‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
