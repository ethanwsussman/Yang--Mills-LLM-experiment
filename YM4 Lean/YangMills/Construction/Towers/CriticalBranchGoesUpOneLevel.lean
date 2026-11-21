import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CriticalBranchUpOneLevel : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ b : CriticalBranchData L n k, b.IsCriticalUpTo i →
      ∃ b' : CriticalBranchData L n k, b'.IsCriticalUpTo (i + 1)
end YangMills.Construction.Tower
end
