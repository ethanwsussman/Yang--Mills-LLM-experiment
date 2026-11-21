import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFew
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace CellCounting
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem card_centredCube (hL : Odd F.blockSide) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by apply _root_.YangMills.Construction.NearTopCoordinates.card_centredCube <;> assumption
theorem sitesPerCellLePow_holds : SitesPerCellLePow := by
  intro F S hL hs z
  classical
  have hmem : ∀ y : ↥(sitesOfCells S F.depth), ∃ w o, o ∈ centredCube F.blockSide ∧
      y.1 = cellCentre F.depth w + siteOfCoords F.depth o := by
    intro y
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 y.2
    obtain ⟨o, ho, hz⟩ := Finset.mem_image.1 hw
    rw [top_sub_depth, pow_one] at ho
    exact ⟨w, o, ho, hz.symm⟩
  choose wf of ho hy using hmem
  rw [← card_centredCube hL]
  refine Finset.card_le_card_of_injOn of (fun y _ => ho y) ?_
  intro y hy₁ y' hy₂ he
  have c1 := (Finset.mem_filter.1 hy₁).2
  have c2 := (Finset.mem_filter.1 hy₂).2
  rw [hy y, enclosingCell_cellCentre_add hL _ _ (ho y)] at c1
  rw [hy y', enclosingCell_cellCentre_add hL _ _ (ho y')] at c2
  apply Subtype.ext
  rw [hy y, hy y', c1, c2, he]
end CellCounting
end YangMills.Construction
end
