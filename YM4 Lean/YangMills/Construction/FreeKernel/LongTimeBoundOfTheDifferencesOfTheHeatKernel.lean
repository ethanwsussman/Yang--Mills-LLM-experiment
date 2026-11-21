import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
open YangMills.Construction.FourDimKernel
def HeatKernelDiffLongTimeBound : Prop :=
  ∀ (k : ℕ) (a : DiffKind) (s : ℝ), 1 ≤ s → ∀ m : ℤ,
    ‖diffOp a (discreteHeatKernel s) m‖ ≤
      (kernelDerivativeBound k).toReal * s ^ (-(((diffOrder a : ℝ) + 1) / 2)) *
        bracketOnePlus (|(m : ℝ)| / Real.sqrt s) ^ (-(k : ℝ))
end YangMills.Construction.FreeKernel
end
