import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
def rightTranslationDerivUniqueStatement : Prop :=
  ∀ w X u u' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X u →
    IsRightTranslationDeriv w X u' → u = u'
end ResponseInTheExpansion
end YangMills.Construction
end
