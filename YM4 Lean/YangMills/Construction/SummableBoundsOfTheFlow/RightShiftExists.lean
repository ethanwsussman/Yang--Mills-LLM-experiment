import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages
def rightTranslationDerivExistsStatement : Prop :=
  ∃ D : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
    ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (D w X)
end YangMills.Construction.Interpolation
end
