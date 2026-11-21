import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem chosenBranchIsCritical_holds
    (hExists : CriticalBranchExists)
    (hNhd : FibreNeighbourhoodsOfSteps) :
    ChosenBranchIsCritical := by
  intro L m k hL hm
  have hc : (chosenCriticalBranch L m k).IsCritical :=
    Classical.epsilon_spec (hExists L m k hL hm)
  refine ⟨hc, fun i hi => ?_⟩
  exact Classical.epsilon_spec (hNhd.2.2.2 L m k hL hm (by omega) _ hc i hi)
end YangMills.Construction.Tower
end
