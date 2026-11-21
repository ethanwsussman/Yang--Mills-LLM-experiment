import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SeveralVariables
def KernelDiagonalsAreDims : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural) (κ : HalfNatural),
    KernelDiagonalEqDim l κ
end YangMills.Construction.SpinHarmonics.SeveralVariables
end
