import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Interpolation
def RightTranslationDerivUnique : Prop :=
  ∀ w X u u' : imaginaryQuaternions, ‖w‖ < Real.pi →
    IsRightTranslationDeriv w X u → IsRightTranslationDeriv w X u' → u = u'
end YangMills.Construction.Interpolation
end
