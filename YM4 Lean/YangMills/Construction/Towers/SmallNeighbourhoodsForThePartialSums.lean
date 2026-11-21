import YangMills.Construction.Towers.PartialSumsOfTheGaugeFixingFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def SmallNhdsForPartialGaugedActions : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ U₀ : Set (Tower.Edge L n k 0 → Matrices.ComplexMatrix2), Tower.IsOpenNhdOfOne U₀ →
      ∃ W : Set (Tower.Edge L n k 0 → Matrices.ComplexMatrix2), Tower.IsOpenNhdOfOne W ∧ W ⊆ U₀ ∧
        (∀ i ≤ k, Tower.IsAnalyticFieldFunction W (Tower.partialGaugedAction L n k i)) ∧
        Tower.IsAnalyticFieldMap W (Tower.smoothingIter L n k k) ∧
        ∀ V ∈ W, Tower.HasSurjectiveDifferential (Tower.smoothingIter L n k k) V
end YangMills.Construction.Tower
end
