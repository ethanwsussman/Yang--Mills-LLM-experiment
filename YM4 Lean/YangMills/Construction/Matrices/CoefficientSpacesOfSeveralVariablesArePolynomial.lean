import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SeveralVariables
def CoeffSpansArePolynomial : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural) (κ : HalfNatural),
    IsStarClosedPolySpan (truncatedCoeffSpan J κ) ∧
    IsStarClosedPolySpan (prodCoeffSpan l)
end YangMills.Construction.SpinHarmonics.SeveralVariables
end
