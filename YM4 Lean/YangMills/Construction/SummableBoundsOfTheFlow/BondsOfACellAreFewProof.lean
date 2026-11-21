import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.SummableBoundsOfTheFlow.BondsOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFewProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
namespace CellBonds
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem enclosingCell_centre_add (hL : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.CellCounting.enclosingCell_cellCentre_add <;> assumption
theorem cellOffset_centre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem card_centredCube (hL : Odd F.blockSide) :
    (centredCube F.blockSide).card = F.blockSide ^ 4 := by apply _root_.YangMills.Construction.NearTopCoordinates.card_centredCube <;> assumption
end CellBonds
open CellBonds in
theorem cellBondsCard (hB : BlocksCoverLowerLevel) : cellBondsCardStatement := by
  intro F hL hs z
  classical
  have hs0 : ∀ i, 0 < F.extent i := fun l => by have := hs l; omega
  have hmem : ∀ b : ↥(chordBonds (finiteCells F)), ∃ y o, o ∈ centredCube F.blockSide ∧
      b.1.1 = cellCentre F.depth y + siteOfCoords F.depth o := by
    intro b
    have hx := hB F hL hs0 b.1.1
    obtain ⟨y, -, hxz⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨o, ho, hzo⟩ := Finset.mem_image.1 hxz
    rw [top_sub_depth, pow_one] at ho
    exact ⟨y, o, ho, hzo.symm⟩
  have hcard : (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))).card =
      4 * F.blockSide ^ 4 := by
    rw [Finset.card_product, card_centredCube hL]
    simp [mul_comm]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun b => (cellOffset b.1.1, b.1.2)) ?_ ?_
  · intro b _
    obtain ⟨y, o, ho, hb⟩ := hmem b
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    rw [hb, cellOffset_centre_add hL hs y o ho]
    exact ho
  · intro b hb b' hb' he
    have hz := (Finset.mem_filter.1 hb).2
    have hz' := (Finset.mem_filter.1 hb').2
    obtain ⟨y, o, ho, e1⟩ := hmem b
    obtain ⟨y', o', ho', e2⟩ := hmem b'
    simp only [Prod.mk.injEq] at he
    rw [e1, enclosingCell_centre_add hL y o ho] at hz
    rw [e2, enclosingCell_centre_add hL y' o' ho'] at hz'
    have h1 := he.1
    rw [e1, e2, cellOffset_centre_add hL hs y o ho, cellOffset_centre_add hL hs y' o' ho'] at h1
    apply Subtype.ext
    apply Prod.ext
    · rw [e1, e2, hz, hz', h1]
    · exact he.2
end YangMills.Construction.Estimates
end
