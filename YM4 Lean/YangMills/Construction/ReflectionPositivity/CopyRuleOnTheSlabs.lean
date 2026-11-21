import YangMills.Construction.ReflectionPositivity.CopiesOnTheSlabsAndTheFold
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def SlabCopyRule : Prop :=
  ∀ (S : SlabDecomposition) (j : ZMod (2 * S.count)) (f : S.period.QuotientField → ℂ),
    f ∈ S.slabAlgebraOfClass j →
    (∀ k : ZMod (2 * S.count), S.slabCopy j k f ∈ S.slabAlgebraOfClass k) ∧
    S.slabCopy j j f = f ∧
    (∀ k : ZMod (2 * S.count),
      PeriodSublattice.supNorm (S.slabCopy j k f) = PeriodSublattice.supNorm f) ∧
    ((∀ U, (f U).im = 0) → ∀ k : ZMod (2 * S.count),
      (∀ U, (S.slabCopy j k f U).im = 0) ∧ ⨅ U, (S.slabCopy j k f U).re = ⨅ U, (f U).re) ∧
    (∀ s i : ZMod (2 * S.count),
      S.conjReflectOfClass s (S.slabCopy j (s + i) f) = S.slabCopy j (s - 1 - i) f)
end YangMills.Construction.InfiniteLattice
