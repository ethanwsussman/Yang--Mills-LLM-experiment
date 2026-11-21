import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators
def SandwichKernelRelabelStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (B B' : Type) [Finite B] [Nonempty B] [Finite B'] (e : B → B')
    (X : HaarL2 B →L[ℂ] HaarL2 B),
    Function.Bijective e → KernelRelabelEquivariant β e X
end YangMills.Construction.TransferOperators
end
