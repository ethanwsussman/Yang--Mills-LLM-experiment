import YangMills.Construction.TransferOperators.ReflectionInALinkMirrorSymmetricStacksAndTheReversal
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators
def IsReversalInvariantOnCenteredStack (μ : Fin 4) (ν : Measure (GaugeField 1)) (i k : ℤ)
    (hk : 1 ≤ k) : Prop :=
  ∀ (v : Set (SliceSite μ)) [Finite v]
    (Ψ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ),
    (linksWithin v).Nonempty → IsRealEntryPolynomial Ψ →
    IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v) Ψ →
    ∫ U, Ψ (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
      ∫ U, levelReversal i k v Ψ
        (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν
end YangMills.Construction.TransferOperators
end
