import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def RealPolyDenseOnPowers : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], SeveralVariables.RealPolyDense J
end YangMills.Construction.SpinHarmonics
end
