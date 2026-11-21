import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Interpolation
variable {F : BlockFrame}
def blockGapObservable (a ρA : ℝ) (m : ℕ) (p : ℝ → ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
    deriv p ‖η b‖ * ‖η b‖⁻¹ *
      ⟪((toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ]), ((frameGap a ρA m b.1 V : imaginaryQuaternions) : ℍ[ℝ])⟫ else 0
end YangMills.Construction.Interpolation
end
