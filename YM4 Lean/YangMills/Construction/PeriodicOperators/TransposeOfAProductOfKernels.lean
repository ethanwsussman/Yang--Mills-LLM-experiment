import YangMills.Construction.PeriodicOperators.TransposesOfProductsAndOfDiagonalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeComp
def Claim : Prop :=
  ∀ (A A' A'' : KernelDomain) (T : A'.Elem → A.Elem → ℂ)
    (S : A.Elem → A''.Elem → ℂ),
    (∀ i' i'', CompSummableAt T S i' i'') →
      (∀ i'' i', CompSummableAt (wTranspose A''.weight A.weight S)
        (wTranspose A.weight A'.weight T) i'' i') ∧
      compKernel (wTranspose A''.weight A.weight S) (wTranspose A.weight A'.weight T) =
        wTranspose A''.weight A'.weight (compKernel T S)
end YangMills.Construction.PeriodicOperators.TransposeComp
end
