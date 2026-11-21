import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ChosenBranchIsCritical : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    (chosenCriticalBranch L n k).IsCritical ∧
      ∀ i < k, (chosenCriticalBranch L n k).IsFibreNhd i (chosenFibreNhd L n k i)
end YangMills.Construction.Tower
end
