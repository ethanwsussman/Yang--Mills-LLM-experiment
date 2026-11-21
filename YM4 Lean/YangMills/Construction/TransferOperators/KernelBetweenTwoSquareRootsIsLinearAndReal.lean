import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators
def SandwichKernelLinearStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (B : Type) [Finite B] [Nonempty B], KernelLinearReal β B
end YangMills.Construction.TransferOperators
end
