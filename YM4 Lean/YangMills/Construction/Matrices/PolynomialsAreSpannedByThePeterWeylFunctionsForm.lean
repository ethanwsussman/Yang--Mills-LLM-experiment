import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
def PolynomialIffInPeterWeylSpan : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (F : (J → specialUnitary) → ℂ),
    IsEntryPolynomial F ↔
      IsRealizedIn F
        (Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))))
end YangMills.Construction.SpinHarmonics
end
