import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Mathlib
set_option autoImplicit false
open Filter Set
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def SubsequentialLimitsAlongPairs : Prop :=
  ∀ Y : FiveBoundSystem, ∀ g ∈ Ioc 0 Y.top,
    (∃ (Q : PairSequence Y.L (Y.IsPair g)) (S : LimitTheorem.CumulantFamily), Q.Defines S) ∧
    ∀ Q : PairSequence Y.L (Y.IsPair g), ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop)
      (S : LimitTheorem.CumulantFamily), (Q.subseq φ hφ).Defines S
end YangMills.Construction.SystemsWithFiveBounds
end
