import YangMills.Construction.TransferOperators.ReversalInvarianceOnASymmetricStack
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
namespace YangMills.Construction.TransferOperators
def ReversalInvariantSuccStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
    ∀ (i k : ℤ) (hk : 1 ≤ k), IsReversalInvariantOnCenteredStack μ ν i k hk →
      IsReversalInvariantOnCenteredStack μ ν i (k + 1) (by omega)
end YangMills.Construction.TransferOperators
