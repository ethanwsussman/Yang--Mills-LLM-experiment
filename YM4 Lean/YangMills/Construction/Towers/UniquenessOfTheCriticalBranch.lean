import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CriticalBranchUnique : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ β : CriticalBranchData L n k, β.IsCritical →
      (∀ l ≤ k, EventuallyNearIdentity (fieldSpace L n k l) fun V =>
        β.energy l V = chosenEnergy L n k l V) ∧
      ∀ l < k, EventuallyNearIdentity (fieldSpace L n k (l + 1)) fun W =>
        β.prolong l W = chosenProlong L n k l W
end YangMills.Construction.Tower
end
