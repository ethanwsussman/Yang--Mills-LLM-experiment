import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
def AllRealPolyDisjointUnionSplit : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], RealPolyDisjointUnionSplit J
end YangMills.Construction.SpinHarmonics
end
