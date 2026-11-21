import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def chartedContourAverage (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) (ζ : StepVariable (finiteCells F)) : ℍ[ℝ] :=
  contourAverage (chartedField (fun x i => w x i + stepCoordinates ζ x i) V) c
def ChartedContourAverageSmooth : Prop :=
  ∀ L : ℕ, Odd L → ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4) (p : StepVariable (finiteCells F)),
    F.blockSide = L → (∀ i, 2 ≤ F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1) →
    ContDiff ℝ 3 (chartedContourAverage w V c) ∧
    ∀ u v : StepVariable (finiteCells F),
      ‖fderiv ℝ (chartedContourAverage w V c) p u‖ ≤ C * ‖u‖ ∧
      ‖fderiv ℝ (fun z => fderiv ℝ (chartedContourAverage w V c) z u) p v‖ ≤ C * ‖u‖ * ‖v‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
