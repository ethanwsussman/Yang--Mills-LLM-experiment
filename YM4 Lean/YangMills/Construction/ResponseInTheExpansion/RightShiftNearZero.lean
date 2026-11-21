import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open BlockAverages Interpolation
def RightTranslationDerivUniqueNearZero : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ w X u u' : imaginaryQuaternions, ‖w‖ < r₀ →
    IsRightTranslationDeriv w X u → IsRightTranslationDeriv w X u' → u = u'
end YangMills.Construction.LinearResponse
end
