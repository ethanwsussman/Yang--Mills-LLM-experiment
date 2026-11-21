import YangMills.Construction.TransferOperators.ReversalInvarianceOnASymmetricStack
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators.ReversalInvariantContinuousNextStack
def Statement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
    ∀ (i k : ℤ) (hk : 1 ≤ k), IsReversalInvariantOnCenteredStack μ ν i k hk →
    ∀ (v : Set (SliceSite μ)) [Finite v]
      (Ψ : C(centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary, ℂ)),
      (linksWithin v).Nonempty → (∀ u, (Ψ u).im = 0) →
      ∫ U, Ψ (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
        ∫ U, levelReversal i k v Ψ
          (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν
end YangMills.Construction.TransferOperators.ReversalInvariantContinuousNextStack
end
