import YangMills.Construction.Torus.AverageOfABondReadsItsDomain
import YangMills.Construction.Torus.ProfilesAndTestForms
import YangMills.Construction.Torus.DifferencesAndAveragesOnAGeneralTorus
import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace CoarseTestFormMeansAux
theorem admitsPartition_levelSpacing (D : ScaleData) {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
theorem set_antitone {D : ScaleData} (B : SeparatedChain D) {m n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ D.lastLevel) : B.set n ⊆ B.set m := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n hmn ih => exact (B.mono n (by omega)).trans (ih (by omega))
end CoarseTestFormMeansAux
end YangMills.Construction.GeneralTorus
