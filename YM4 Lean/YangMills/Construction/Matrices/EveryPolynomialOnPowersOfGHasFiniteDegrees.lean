import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.PolynomialDegrees
open YangMills.Construction.SpinHarmonics.SeveralVariables
def Statement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], PolyHasFiniteDegrees J
end YangMills.Construction.SpinHarmonics.PolynomialDegrees
end
