import YangMills.Construction.RunningCouplingSlope.PlainChainOfATangent
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ShiftedGaugeMapAtQuietPoint : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U => ∀ ξ : LevelForms L n k,
      (∀ j ≤ k, tangentForms U ξ j ∈ edgeFormSpace L n k j) ∧
        (shiftedGaugeMap (quietPoint U) ξ : Edge L n k k → Matrices.ComplexMatrix2) = tangentForms U ξ k
end YangMills.Construction.RunningCouplingSlope
end
