import YangMills.Construction.TransferOperators.SquareRootOfTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics
def sqrtLinkKernelSlice (β : ℝ) {B : Type} [Finite B]
    (u : B → Matrices.ComplexMatrix2.specialUnitary) : HaarL2 B :=
  toHaarL2 fun w => sqrtLinkKernel β w u
def sqrtKernelSandwich (β : ℝ) {B : Type} [Finite B]
    (X : HaarL2 B →L[ℂ] HaarL2 B) (u v : B → Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  inner ℂ (sqrtLinkKernelSlice β u) (X (sqrtLinkKernelSlice β v))
end YangMills.Construction.TransferOperators
end
