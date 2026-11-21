import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices
open scoped ComplexOrder
namespace TransferOperators.LogKernelRatio
def RealLocalInvariantStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (B : Block μ) (Ξ : B.L2Operator),
    ‖Ξ‖ ≤ 1 → IsRealPreserving Ξ →
    (∀ g : B.vertices → ComplexMatrix2.specialUnitary, Commute Ξ (blockGaugeRep B g)) →
    (∀ u u' : ↥(B.links : Set (SliceLink μ)) → ComplexMatrix2.specialUnitary,
      0 < sqrtKernelSandwich β Ξ u u') →
    ∀ n : ℤ, B.LogKernelRatioIsRealLocalInvariant β Ξ n
end TransferOperators.LogKernelRatio
end YangMills.Construction
end
