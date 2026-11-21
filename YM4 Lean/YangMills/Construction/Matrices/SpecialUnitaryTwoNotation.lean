import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
abbrev adjointMatrix (X : ComplexMatrix2) : ComplexMatrix2 := X.conjTranspose
theorem matExp_eq_tsum (Z : ComplexMatrix2) :
    matExp Z = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • Z ^ n :=
  congrFun (NormedSpace.exp_eq_tsum ℂ) Z
abbrev realLog (x : ℝ) : ℝ := Real.log x
end YangMills.Construction.Matrices.ComplexMatrix2
