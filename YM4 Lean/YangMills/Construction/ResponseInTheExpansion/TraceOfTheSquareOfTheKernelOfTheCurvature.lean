import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
def CurvatureKernelSqTraceFormula : Prop :=
  ∀ z : Fin 4 → ℝ, 0 < sqNorm z →
    ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ τ : Fin 4,
      (if μ < ν ∧ ρ < τ then continuumCurvatureKernel z μ ν ρ τ ^ 2 else 0) = 6 / (Real.pi ^ 4 * sqNorm z ^ 4)
end YangMills.Construction.LinearResponse
end
