import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def MonomialFactorDerivativeBounds : Prop :=
  (∀ (a : DiffKind) (k : ℕ) (t : ℝ),
    ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a) t‖ ≤
      symmetryConstant * |t| ^ (diffOrder a - k)) ∧
  (∀ (a : DiffKind) (n k : ℕ), k ≤ n → ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
    ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (symbolError x : ℂ)) t‖ ≤
      2 ^ (n + 1) * Real.pi ^ 2 * symmetryConstant * |t| ^ (diffOrder a + 4 - k))
end YangMills.Construction.FreeKernel
end
