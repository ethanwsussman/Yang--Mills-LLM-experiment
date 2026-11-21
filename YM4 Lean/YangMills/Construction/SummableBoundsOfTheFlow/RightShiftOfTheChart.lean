import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def rightTranslationChartStatement : Prop :=
  ∃ (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions) (C : ℝ), 0 ≤ C ∧
    (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) ∧
    (∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th w) ∧
    ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th w‖ ≤ C
end Interpolation
end YangMills.Construction
end
