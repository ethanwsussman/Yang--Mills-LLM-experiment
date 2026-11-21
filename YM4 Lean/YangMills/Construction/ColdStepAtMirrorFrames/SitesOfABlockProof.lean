import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace BlockSites
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
def halfWidth (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem mem_centredCube_iff {L : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -halfWidth L ≤ h i ∧ h i ≤ halfWidth L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem enclosingCell_shift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset <;> assumption
theorem cellOffset_shift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem unitStep_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : (unitStep F.top i : F.Cell) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem shift_add_unitStep (z : F.Cell) (h : Fin 4 → ℤ) (i : Fin 4) :
    (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (h + Pi.single i 1) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem cellCentre_add_unitStep (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (z + unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellCentre_add_unitStep <;> assumption
theorem isCrossingBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) ↔
      h i = halfWidth F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff <;> assumption
theorem enclosingCell_next (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) = z ∨
      enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
        z + unitStep F.top i := by
  have hc := (mem_centredCube_iff h).mp hh
  by_cases he : h i = halfWidth F.blockSide
  · right
    set h' : Fin 4 → ℤ := h + Pi.single i (1 - (F.blockSide : ℤ)) with hh'
    obtain ⟨k, hk⟩ := hL
    have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    have hk2 : halfWidth F.blockSide = k := by
      unfold halfWidth
      rw [hLz]
      omega
    have hin : h' ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [hh', Pi.add_apply, Pi.single_eq_same, he]
        rw [hk2, hLz]
        constructor <;> linarith
      · simp only [hh', Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hc l
    have e : (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
        cellCentre F.depth (z + unitStep F.top i) + siteOfCoords F.depth h' := by
      rw [cellCentre_add_unitStep hs, shift_add_unitStep]
      have e2 : (siteOfCoords F.depth (h + Pi.single i 1) : F.Site F.depth) =
          siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) + siteOfCoords F.depth h' := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp [siteOfCoords, hh']
          ring
        · simp [siteOfCoords, hh', Pi.single_eq_of_ne hl]
      rw [e2, add_assoc]
    rw [e, enclosingCell_shift ⟨k, hk⟩ hs _ h' hin]
  · left
    have hin : h + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [Pi.add_apply, Pi.single_eq_same]
        have := hc l
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hc l
    rw [shift_add_unitStep, enclosingCell_shift hL hs z _ hin]
end BlockSites
open BlockSites in
theorem siteDecomposition_of_blocksCover (hcover : BlocksCoverLowerLevel) : SiteDecomposition := by
  intro F hL hs
  have hdecomp : ∀ x : F.Site F.depth, ∃ (z : F.Cell) (h : Fin 4 → ℤ), h ∈ centredCube F.blockSide ∧
      x = cellCentre F.depth z + siteOfCoords F.depth h := by
    intro x
    have hx := hcover F hL (fun i => by have := hs i; omega) x
    unfold sitesOfCells at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨z, _, hz⟩ := hx
    rw [Finset.mem_image] at hz
    obtain ⟨h, hh, e⟩ := hz
    rw [top_sub_depth, pow_one] at hh
    exact ⟨z, h, hh, e.symm⟩
  refine ⟨fun z h hh => ⟨enclosingCell_shift hL hs z h hh, cellOffset_shift hL hs z h hh⟩, fun x => ?_,
    fun x i => ?_, fun x i => ?_⟩
  · obtain ⟨z, h, hh, rfl⟩ := hdecomp x
    rw [enclosingCell_shift hL hs z h hh, cellOffset_shift hL hs z h hh]
    exact ⟨rfl, hh⟩
  · obtain ⟨z, h, hh, rfl⟩ := hdecomp x
    rw [isCrossingBond_iff hL hs z h hh i, cellOffset_shift hL hs z h hh]
    rfl
  · obtain ⟨z, h, hh, rfl⟩ := hdecomp x
    rw [enclosingCell_shift hL hs z h hh]
    exact enclosingCell_next hL hs z h hh i
end YangMills.Construction.ColdStepAtMirrorFrames
end
