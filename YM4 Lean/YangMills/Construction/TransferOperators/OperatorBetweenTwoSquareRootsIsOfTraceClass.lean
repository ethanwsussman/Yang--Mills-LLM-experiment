import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators
def SandwichTraceClassStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (B : Type) [Finite B] [Nonempty B]
    (X : HaarL2 B →L[ℂ] HaarL2 B), SandwichTraceClassWithKernel β X
end YangMills.Construction.TransferOperators
end
