import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def Ambient.translationContinuousC1Norm : Prop :=
  ∀ (M : SharpParameter) (p : Conventions.StandingParameters) (X : Ambient),
    X.TranslationContinuityC1 p M
end YangMills.Construction.LimitSpaces
end
