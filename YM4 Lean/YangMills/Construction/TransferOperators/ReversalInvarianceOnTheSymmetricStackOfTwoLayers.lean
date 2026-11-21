import YangMills.Construction.TransferOperators.ReversalInvarianceOnASymmetricStack
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
namespace YangMills.Construction.TransferOperators
def ReversalInvariantTwoLevelStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
    ∀ i : ℤ, IsReversalInvariantOnCenteredStack μ ν i 1 le_rfl
end YangMills.Construction.TransferOperators
