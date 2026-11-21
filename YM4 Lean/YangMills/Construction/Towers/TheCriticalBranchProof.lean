import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevel
import YangMills.Construction.Towers.CriticalBranchGoesUpOneLevel
import YangMills.Construction.Towers.TheCriticalBranch
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem criticalBranch_exists (hBottom : BottomLevelCriticalBranch)
    (hUp : CriticalBranchUpOneLevel) : CriticalBranchExists := by
  intro L n k hL hn
  have key : ∀ m, m ≤ k → ∃ b : CriticalBranchData L n k, b.IsCriticalUpTo m := by
    intro m
    induction m with
    | zero => intro _; exact hBottom L n k hL hn
    | succ m ih =>
      intro hm
      obtain ⟨b, hb⟩ := ih (by omega)
      exact hUp L n k m hL hn (by omega) b hb
  exact key k le_rfl
end YangMills.Construction.Tower
