import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
def ContinuumCurvatureKernelBoundAndLipschitz : Prop :=
  ∀ (r : ℝ) (z z' : Fin 4 → ℝ) (μ ν ρ τ : Fin 4), 0 < r → r ^ 2 ≤ sqNorm z → r ^ 2 ≤ sqNorm z' →
    |continuumCurvatureKernel z μ ν ρ τ| ≤ 18 / r ^ 4 ∧
    |continuumCurvatureKernel z μ ν ρ τ - continuumCurvatureKernel z' μ ν ρ τ| ≤
      200 * Real.sqrt (sqNorm (z - z')) / r ^ 5
end YangMills.Construction.LinearResponse
end
