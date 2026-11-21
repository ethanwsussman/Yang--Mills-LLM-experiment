import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
def AllPolyMulShiftSpins : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural), PolyMulShiftsSpins l
end YangMills.Construction.SpinHarmonics
end
