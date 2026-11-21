import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.CountOfTheBonds
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace BondCount
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
def halfWidth (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem mem_centredCube_iff {L : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -halfWidth L ≤ h i ∧ h i ≤ halfWidth L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem enclosingCell_shift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset <;> assumption
theorem cellOffset_shift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem unitStep_top_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    (unitStep F.top i : F.Cell) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem shift_add_unitStep (z : F.Cell) (h : Fin 4 → ℤ) (i : Fin 4) :
    (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (h + Pi.single i 1) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem cellCentre_add_unitStep (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (z + unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellCentre_add_unitStep <;> assumption
def IsAxialTreeOffset (L : ℕ) (e : (Fin 4 → ℤ) × Fin 4) : Prop :=
  e.1 e.2 ≠ halfWidth L ∧ ∀ l, e.2 < l → e.1 l = 0
theorem isAxialTreeBond_shift_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) ↔
      IsAxialTreeOffset F.blockSide (h, i) := by apply _root_.YangMills.Construction.TopLevelSites.isAxialTreeBond_iff <;> assumption
end BondCount
open BondCount in
theorem bondCount_of_blocksCover (hcover : BlocksCoverLowerLevel) : BondCount := by
  classical
  intro L hL
  set T0 : Finset ((Fin 4 → ℤ) × Fin 4) :=
    ((centredCube L) ×ˢ Finset.univ).filter fun e => ¬ IsAxialTreeOffset L e with hT0
  refine ⟨T0.card, fun F n hFL hn hside => ?_⟩
  subst hFL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; exact hn
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hmem := mem_finiteCells (F := F) hs
  constructor
  · have htop : sitesOfCells (finiteCells F) F.top = finiteCells F := by
      ext y
      constructor
      · intro _
        exact hmem y
      · intro hy
        unfold sitesOfCells
        rw [Finset.mem_biUnion]
        refine ⟨y, hy, ?_⟩
        rw [Finset.mem_image]
        refine ⟨0, ?_, ?_⟩
        · rw [Nat.sub_self, pow_zero, mem_centredCube_iff]
          intro i
          simp [halfWidth]
        · funext i
          simp [cellCentre, siteOfCoords, siteCoords]
    have hall : innerBonds (finiteCells F) F.top = finiteCells F ×ˢ Finset.univ := by
      unfold innerBonds
      rw [htop, Finset.filter_true_of_mem]
      intro b _
      exact hmem _
    rw [hall, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  · have hcov := hcover F hL hpos
    have hcard : ((finiteCells F) ×ˢ T0).card = (chordBonds (finiteCells F)).card := by
      apply Finset.card_bij (fun (e : F.Cell × ((Fin 4 → ℤ) × Fin 4)) _ =>
        (((cellCentre F.depth e.1 + siteOfCoords F.depth e.2.1 : F.Site F.depth), e.2.2) :
          F.Site F.depth × Fin 4))
      · rintro ⟨z, h, i⟩ he
        have h1 := (Finset.mem_product.mp he).2
        have h2 := (Finset.mem_filter.mp h1)
        have hh : h ∈ centredCube F.blockSide := (Finset.mem_product.mp h2.1).1
        unfold chordBonds innerBonds
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_product.mpr ⟨hcov _, Finset.mem_univ _⟩, hcov _⟩, ?_⟩
        simp only
        rw [isAxialTreeBond_shift_iff hL hs z h hh i]
        exact h2.2
      · rintro ⟨z, h, i⟩ he ⟨z', h', i'⟩ he' heq
        have hh : h ∈ centredCube F.blockSide :=
          (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp he).2).1).1
        have hh' : h' ∈ centredCube F.blockSide :=
          (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp he').2).1).1
        simp only [Prod.mk.injEq] at heq
        have e1 : z = z' := by
          have := congrArg enclosingCell heq.1
          rwa [enclosingCell_shift hL hs z h hh, enclosingCell_shift hL hs z' h' hh'] at this
        have e2 : h = h' := by
          have := congrArg cellOffset heq.1
          rwa [cellOffset_shift hL hs z h hh, cellOffset_shift hL hs z' h' hh'] at this
        rw [e1, e2, heq.2]
      · rintro ⟨x, i⟩ hb
        unfold chordBonds at hb
        have hnt := (Finset.mem_filter.mp hb).2
        have hx := hcov x
        unfold sitesOfCells at hx
        obtain ⟨z, hz, hx2⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨h, hh, hxe⟩ := Finset.mem_image.mp hx2
        rw [top_sub_depth, pow_one] at hh
        refine ⟨(z, (h, i)), ?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨hz, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
          · exact Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩
          · rw [← hxe] at hnt
            rwa [isAxialTreeBond_shift_iff hL hs z h hh i] at hnt
        · simp only
          rw [hxe]
    rw [← hcard, Finset.card_product, mul_comm]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
