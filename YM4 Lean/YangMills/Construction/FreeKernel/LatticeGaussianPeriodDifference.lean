import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex MeasureTheory
open YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def LatticeGaussianDifferenceOnPeriod : Prop :=
  ∀ (n : ℕ) (a : DiffKind) (t : ℝ), 1 ≤ t →
    ∫⁻ x in Set.Icc (-Real.pi) Real.pi,
        ‖iteratedDeriv n (fun y : ℝ => diffMultiplier a y * (Real.exp (-t * laplacianSymbol y) : ℂ) -
          (I * (y : ℂ)) ^ diffOrder a * (Real.exp (-t * y ^ 2) : ℂ)) x‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
        (binomialMoment n (diffOrder a + 1) +
          ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) * binomialMoment n (diffOrder a + 4)) *
        ENNReal.ofReal (t ^ (((n : ℝ) - diffOrder a - 2) / 2))
end YangMills.Construction.FreeKernel
end
