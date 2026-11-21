import YangMills.Construction.SoftAverages.FunctionsOfFinitelyManyLinks
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.SoftAverages.FieldMoves
open FiniteLinkFunctions
theorem expImag_zero : expImag 0 = 1 := by
  rw [expImag_eq_exp]
  simp
end YangMills.Construction.SoftAverages.FieldMoves
end
