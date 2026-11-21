import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices
open scoped ComplexOrder
namespace TransferOperators.LogKernelRatio
def NonposStateStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (B : Block μ) (Ξ : B.L2Operator),
    ‖Ξ‖ ≤ 1 → IsRealPreserving Ξ →
    (∀ g : B.vertices → ComplexMatrix2.specialUnitary, Commute Ξ (blockGaugeRep B g)) →
    (∀ u u' : ↥(B.links : Set (SliceLink μ)) → ComplexMatrix2.specialUnitary,
      0 < sqrtKernelSandwich β Ξ u u') →
    ∀ n : ℤ, ∀ ν : MeasureTheory.Measure (GaugeField 1), IsPeriodicGibbs β ν →
      stateEval ν (B.logKernelRatio β Ξ n) ≤ 0
end TransferOperators.LogKernelRatio
end YangMills.Construction
end
