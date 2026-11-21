import YangMills.Construction.ResponseInTheExpansion.TraceOfTheSquareOfTheKernelOfTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
theorem curvatureKernelSqTraceFormula_holds : CurvatureKernelSqTraceFormula := by
  intro z hz
  have hnorm : sqNorm z = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
    simp [sqNorm, Fin.sum_univ_four]
  have hinv : (sqNorm z)⁻¹ * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) = 1 := by
    rw [← hnorm]; exact inv_mul_cancel₀ hz.ne'
  have hrewrite : 6 / (Real.pi ^ 4 * sqNorm z ^ 4) = 6 * ((Real.pi ^ 2 * sqNorm z ^ 2)⁻¹) ^ 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hne : sqNorm z ≠ 0 := hz.ne'
    field_simp
  rw [hrewrite]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLT, Fin.reduceEq, lt_self_iff_false, and_true, and_false,
    if_true, if_false, continuumCurvatureKernel, hyperplaneReflection, add_zero, zero_add, div_eq_mul_inv]
  generalize (sqNorm z)⁻¹ = t at hinv ⊢
  generalize (Real.pi ^ 2 * sqNorm z ^ 2)⁻¹ = e
  linear_combination (e ^ 2 * 12 * t * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2)) * hinv
end YangMills.Construction.LinearResponse
end
