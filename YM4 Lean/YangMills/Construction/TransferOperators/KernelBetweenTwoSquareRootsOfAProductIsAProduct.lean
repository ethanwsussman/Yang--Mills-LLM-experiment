import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators
def SandwichKernelProductStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (B : Type) [Finite B] [Nonempty B] (n : ℕ) (parts : Fin n → Set B)
    (R : Set B) (Xs : ∀ i, HaarL2 ↥(parts i) →L[ℂ] HaarL2 ↥(parts i)),
    IsPartitionWithRest parts R → KernelProductFormula β parts R Xs
end YangMills.Construction.TransferOperators
end
