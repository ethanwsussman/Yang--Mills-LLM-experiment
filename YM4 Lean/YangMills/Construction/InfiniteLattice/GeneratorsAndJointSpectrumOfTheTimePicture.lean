import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
def principalArg (z : ℂ) : ℝ := Complex.arg z
end LatticeConventions
end YangMills.Construction
end
