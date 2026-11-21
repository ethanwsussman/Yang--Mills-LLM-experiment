import YangMills.Construction.TransferOperators.ReflectionInALinkMirrorSymmetricStacksAndTheReversal
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
namespace YangMills.Construction.TransferOperators
def CenteredStackClassStatement : Prop :=
  ∀ (μ : Fin 4) (i k : ℤ) (hk : 1 ≤ k) (F : GaugeField 1 → ℂ),
    F ∈ centeredStackClass μ i k hk ↔
      IsGaugeInvariantFunction F ∧ (∀ U, (F U).im = 0) ∧
        ∃ (v : Set (SliceSite μ)) (_ : Finite v), (linksWithin v).Nonempty ∧
          ∃ P : (((centeredStack i k hk).linksOver v : Set (PositiveLink 1)) →
              Matrices.ComplexMatrix2.specialUnitary) → ℂ,
            IsEntryPolynomial P ∧ ∀ U : GaugeField 1, F U = P fun c => U c.1.1
end YangMills.Construction.TransferOperators
