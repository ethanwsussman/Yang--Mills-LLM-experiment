import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.InfiniteLattice YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators
def SandwichKernelGaugeStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (B : Block μ)
    (X : HaarL2 (B.links : Set (SliceLink μ)) →L[ℂ]
      HaarL2 (B.links : Set (SliceLink μ))), KernelGaugeInvariant β B X
end YangMills.Construction.TransferOperators
end
