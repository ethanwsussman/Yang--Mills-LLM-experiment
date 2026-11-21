import YangMills.Construction.Towers.CarriedFamilyIsACriticalBranch
import YangMills.Construction.Towers.CriticalBranchUnderTheDilation
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import YangMills.Construction.Towers.UniquenessOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem chosenBranchScaling_holds
    (hChosen : ChosenBranchIsCritical)
    (hUniq : CriticalBranchUnique)
    (hScaled : ScaledBranchIsCriticalStatement) :
    ChosenBranchScaling := by
  intro L m k j hL hj hs hm hj1
  have hb := hScaled L m k j hL hj hs hm hj1 (chosenCriticalBranch L m k) (hChosen L m k hs hm).1
  exact hUniq L (scaledExponent m k j) j hs (Nat.add_pos_left hm _) _ hb
end YangMills.Construction.Tower
end
