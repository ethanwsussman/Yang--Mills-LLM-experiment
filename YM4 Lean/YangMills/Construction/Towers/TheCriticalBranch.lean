import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CriticalBranchExists : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∃ b : CriticalBranchData L n k, b.IsCritical
end YangMills.Construction.Tower
end
