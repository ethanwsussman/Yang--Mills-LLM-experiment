import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ImaginaryCoordinatesIsometric : Prop :=
  (∀ u v : BondVector, toImaginary (u + v) = toImaginary u + toImaginary v) ∧
  (∀ (c : ℝ) (v : BondVector), toImaginary (c • v) = c • toImaginary v) ∧
  (∀ v : BondVector, ‖toImaginary v‖ = ‖v‖) ∧
  (∀ q : imaginaryQuaternions, ∃ v : BondVector, toImaginary v = q) ∧
  (∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (η ζ : StepVariable (finiteCells F)),
    shiftCoordinates (shiftCoordinates w η) ζ = shiftCoordinates w (η + ζ)) ∧
  (∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions),
    shiftCoordinates w (0 : StepVariable (finiteCells F)) = w) ∧
  ∀ (F : BlockFrame) (w w₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w₂ b.1 b.2) → chartedField w V = chartedField w₂ V
end ColdStepAtMirrorFrames
end YangMills.Construction
end
