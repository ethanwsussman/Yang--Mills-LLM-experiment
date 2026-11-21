import YangMills.Construction.FreeKernel.GreenKernelBounds
import YangMills.Construction.FreeKernel.PoissonInteriorEstimates
import YangMills.Construction.FreeKernel.SecondDifferenceConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open LatticePoisson
def uniformSecondDiffConst (d : ℕ) (ε β : ℝ) : ℝ :=
  (d : ℝ) * kernelConst d * (6 : ℝ) ^ d *
      (5 / ((2 : ℝ) ^ ε - 1) + (2 : ℝ) ^ (d + 1) / (1 - (2 : ℝ) ^ (-(1 - β) / 2)) + 1) +
    kernelConst d ^ 2 * logConstant d ε
def holderFieldInteriorConst (d : ℕ) (ε β : ℝ) : ℝ :=
  (d : ℝ) * max (interiorConst d) (interiorConstOfExponent d (max β (1 / 2))) *
      (1 + (3 : ℝ) ^ ((d : ℝ) / 2) * 2 * (d : ℝ) ^ 2 * kernelConst d ^ 2) +
    (d : ℝ) * uniformSecondDiffConst d ε β
end YangMills.Construction.FreeKernel
