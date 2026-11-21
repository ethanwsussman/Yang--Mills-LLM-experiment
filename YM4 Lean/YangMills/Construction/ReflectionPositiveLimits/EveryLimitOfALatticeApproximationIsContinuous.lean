import YangMills.Construction.ReflectionPositiveLimits.LatticeApproximationsRepresentativesAndLimits
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TestFunctions
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContinuity
def LimitIsContinuous : Prop :=
  ∀ L : ℕ, Odd L → 13 ≤ L →
    ∀ (A : LatticeSequence L) (σ : Tuple → ℝ), A.HasLimit σ →
      (∀ k : ℕ, 0 < k → ∀ S : Fin k → Set Space, (∀ i, IsCompact (S i)) →
        (∀ i i', i ≠ i' → Disjoint (S i) (S i')) →
        ∃ C : ℝ, ∀ X Y : Tuple, X.len = k → Y.len = k →
          (∀ i : Fin k, tsupport (componentAt X i) ∪ tsupport (componentAt Y i) ⊆ S i) →
          (∀ j, |A.mean j X| ≤ C * ∏ i : Fin k, c1NormR4 (componentAt X i)) ∧
            |σ X - σ Y| ≤ C * ∑ i : Fin k, c1NormR4 (componentAt X i - componentAt Y i) *
              ∏ i' ∈ Finset.univ.erase i,
                max (c1NormR4 (componentAt X i')) (c1NormR4 (componentAt Y i'))) ∧
        IsAdmissiblyContinuous σ
end YangMills.Construction.ReflectionPositivity.LimitContinuity
