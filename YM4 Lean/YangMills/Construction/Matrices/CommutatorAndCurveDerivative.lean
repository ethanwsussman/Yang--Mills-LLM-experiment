import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def commutatorMap (X : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun Y := X * Y - Y * X
  map_add' Y Z := by
    simp only [mul_add, add_mul]
    abel
  map_smul' c Y := by
    simp [smul_sub]
section Operators
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
def endomorphismNorm (z : E →ₗ[𝕜] E) : ℝ := ‖LinearMap.toContinuousLinearMap z‖
def expDivisorSeries (z : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  LinearMap.toContinuousLinearMap.symm
    (∑' m : ℕ, LinearMap.toContinuousLinearMap ((((m + 1).factorial : 𝕜)⁻¹) • z ^ m))
end Operators
end YangMills.Construction.Matrices.ComplexMatrix2
