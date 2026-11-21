import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsFollowsABijection
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsBoundedContinuousAndASeries
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsGaugeInvariant
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsLinearAndReal
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsOfAProductIsAProduct
import YangMills.Construction.TransferOperators.OperatorBetweenTwoSquareRootsIsOfTraceClass
import YangMills.Construction.TransferOperators.OperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
theorem sandwichOperator_holds
    (hBounded : SandwichKernelBoundedStatement)
    (hTrace : SandwichTraceClassStatement)
    (hLinear : SandwichKernelLinearStatement)
    (hGauge : SandwichKernelGaugeStatement)
    (hProduct : SandwichKernelProductStatement)
    (hRelabel : SandwichKernelRelabelStatement) :
    SandwichOperatorStatement :=
  fun β hβ =>
    ⟨fun B _ _ X => ⟨hBounded β hβ B X, hTrace β hβ B X⟩,
      fun B _ _ => hLinear β hβ B,
      fun μ B X => hGauge β hβ μ B X,
      fun B _ _ n parts R Xs h => hProduct β hβ B n parts R Xs h,
      fun B B' _ _ _ β₀ X h => hRelabel β hβ B B' β₀ X h⟩
end YangMills.Construction.TransferOperators
end
