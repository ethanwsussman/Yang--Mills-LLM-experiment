import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctions
variable {n : ℕ}
def euclideanNorm (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)
end YangMills.Construction.EuclideanFunctions
