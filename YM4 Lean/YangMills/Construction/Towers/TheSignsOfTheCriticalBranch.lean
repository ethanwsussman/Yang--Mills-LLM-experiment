import YangMills.Construction.Towers.NeighbourhoodForTheFibresOfAStep
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
def chosenCriticalBranch (L n k : ℕ) : CriticalBranchData L n k :=
  Classical.epsilon CriticalBranchData.IsCritical
def chosenFibreNhd (L n k i : ℕ) : Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  Classical.epsilon ((chosenCriticalBranch L n k).IsFibreNhd i)
def chosenEnergy (L n k j : ℕ) : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ :=
  (chosenCriticalBranch L n k).energy j
def chosenProlong (L n k i : ℕ) :
    (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2 :=
  (chosenCriticalBranch L n k).prolong i
def chosenGaugeFixedEnergy (L n k i : ℕ) : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ :=
  (chosenCriticalBranch L n k).gaugeFixedEnergy i
def chosenLevelFibre (L n k i : ℕ) (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) :
    Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  CriticalBranchData.levelFibre (chosenFibreNhd L n k i) W
def chosenProlongComp (L n k j : ℕ) :
    (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k 0 → Matrices.ComplexMatrix2 :=
  (chosenCriticalBranch L n k).prolongComp j
end Tower
end YangMills.Construction
end
