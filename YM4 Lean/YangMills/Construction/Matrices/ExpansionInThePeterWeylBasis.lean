import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def PeterWeylExpansionHolds : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], SeveralVariables.PeterWeylExpansion J
end YangMills.Construction.SpinHarmonics
end
