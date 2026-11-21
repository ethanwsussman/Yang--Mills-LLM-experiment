import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def Ambient.c1WithinComplete : Prop :=
  ∀ (p : Conventions.StandingParameters) (X : Ambient), X.C1WithinIsBanach p
end YangMills.Construction.LimitSpaces
end
