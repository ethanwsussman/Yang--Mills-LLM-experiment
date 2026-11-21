import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex MeasureTheory Filter Topology
open YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def MonomialGaussianDerivativeBounds : Prop :=
  ∀ (a : DiffKind) (t : ℝ), 1 ≤ t → ∀ k : ℕ,
    (∀ x : ℝ, ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (Real.exp (-t * x ^ 2) : ℂ)) x‖ₑ ≤
      ENNReal.ofReal symmetryConstant * binomialMoment k (diffOrder a) *
        ENNReal.ofReal
          (t ^ (((k : ℝ) - diffOrder a) / 2) * Real.exp (-(1 / 2 * heatDecay * t * x ^ 2)))) ∧
    ∫⁻ x : ℝ, ‖iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (Real.exp (-t * x ^ 2) : ℂ)) x‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant * binomialMoment k (diffOrder a) *
        ENNReal.ofReal (t ^ (((k : ℝ) - diffOrder a - 1) / 2)) ∧
    Integrable (iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (Real.exp (-t * x ^ 2) : ℂ))) ∧
    Tendsto (iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (Real.exp (-t * x ^ 2) : ℂ))) atTop (𝓝 0) ∧
    Tendsto (iteratedDeriv k (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder a * (Real.exp (-t * x ^ 2) : ℂ))) atBot (𝓝 0)
end YangMills.Construction.FreeKernel
end
