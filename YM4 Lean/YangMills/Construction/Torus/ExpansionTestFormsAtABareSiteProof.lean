import YangMills.Construction.Torus.ClosedFormsWithVanishingAveragesAreGradientsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.CoarseTestFormsAtBaseSite
section Lattice
variable (D : ScaleData)
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
variable {D}
theorem posBondDir_bondFrom {n : ℕ} (hn : n ≤ D.lastLevel) (x : D.SiteAt n) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.posBondDir_bondFrom <;> assumption
theorem tgt_eq_src_add {n : ℕ} (c : D.PosBond n) :
    c.1.tgt = c.1.src + unitStep D.torusSide (D.levelSpacing n) (ScaleData.posBondDir c) := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.tgt_eq_src_add <;> assumption
end Lattice
section Members
variable {D : ScaleData} (B : SeparatedChain D)
theorem set_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.lastLevel) : B.set j ⊆ B.set i := by apply _root_.YangMills.Construction.GeneralTorus.CoarseTestFormMeansAux.set_antitone <;> assumption
end Members
variable (W : GaugeSetting)
end YangMills.Construction.GeneralTorus.CoarseTestFormsAtBaseSite
