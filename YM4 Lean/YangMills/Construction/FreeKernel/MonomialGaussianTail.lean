import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex MeasureTheory
open YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def MonomialGaussianTailBound : Prop :=
  ∀ (n : ℕ) (a : DiffKind) (t : ℝ), 1 ≤ t →
    ∫⁻ x in {x : ℝ | Real.pi < |x|}, ‖iteratedDeriv n (fun y : ℝ => (I * (y : ℂ)) ^ diffOrder a * (Real.exp (-t * y ^ 2) : ℂ)) x‖ₑ ≤
      ENNReal.ofReal (2 * Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant * binomialMoment n (diffOrder a) *
        ENNReal.ofReal (t ^ (((n : ℝ) - diffOrder a - 2) / 2))
end YangMills.Construction.FreeKernel
end
