import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open YangMills.Construction.InfiniteLattice
open scoped ComplexOrder
def ExpShiftIntegralTraceStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (B : Block μ) (Ξ : B.L2Operator),
    ‖Ξ‖ ≤ 1 → IsRealPreserving Ξ →
    (∀ g : B.vertices → Matrices.ComplexMatrix2.specialUnitary, Commute Ξ (blockGaugeRep B g)) →
    (∀ u u' : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary,
      0 < sqrtKernelSandwich β Ξ u u') →
    ∀ i : ℤ, ∀ Q' : AddSubgroup (LatticePoint 1), Q'.FiniteIndex → B.PairwiseDisjointShifts i Q' →
      ∀ Γ : CubicPeriodSublattice, Γ.lattice.periods ≤ Q' →
        Γ.ExpShiftIntegralEqTrace B β Ξ i Q'
end YangMills.Construction.TransferOperators
end
