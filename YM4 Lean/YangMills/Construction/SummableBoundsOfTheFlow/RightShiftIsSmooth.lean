import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
def rightTranslationSmooth : Prop :=
  ∃ (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions) (C : ℝ), 0 ≤ C ∧
    (∀ w X u : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X u → u = Th w X) ∧
    (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) ∧
    (∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w) ∧
    ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Th w‖ ≤ C
end YangMills.Construction.Interpolation
end
