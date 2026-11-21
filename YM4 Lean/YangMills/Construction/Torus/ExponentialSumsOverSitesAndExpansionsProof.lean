import YangMills.Construction.Torus.AveragesOfTheExpansionTestFormsProof
import YangMills.Construction.Torus.ObjectsOfASequenceOfRegionsOnAGeneralTorusProof
import YangMills.Construction.Torus.SumsOverTheSitesOfASeparatedSequenceProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus.ScaledDistExpSums
section Geometry
variable {D : ScaleData} (B : SeparatedChain D)
end Geometry
theorem isEvenMultipleOf_levelSpacing (D : ScaleData) {n : ℕ} (hn : n ≤ D.lastLevel) :
    IsEvenMultipleOf D.torusSide (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.isEvenMultipleOf_levelSpacing <;> assumption
theorem one_le_L (D : ScaleData) : (1 : ℝ) ≤ D.L := by
  have := D.blocking.thirteen_le
  exact_mod_cast (by omega : 1 ≤ D.L)
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem shellSitesUnion_finite {D : ScaleData} (B : SeparatedChain D) : B.shellSitesUnion.Finite := by
  refine Set.Finite.biUnion (Set.finite_Iic _) fun n hn => ?_
  have hfin : (spacingLattice D.torusSide (D.levelSpacing n) : Set D.Space).Finite :=
    Set.finite_coe_iff.mp (finite_latticeSite (isEvenMultipleOf_levelSpacing D hn))
  exact hfin.subset Set.inter_subset_left
end GeneralTorus.ScaledDistExpSums
end YangMills.Construction
end
