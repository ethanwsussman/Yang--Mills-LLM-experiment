import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.CountOfTheChartBondsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
namespace StepSettings
variable {F : BlockFrame}
namespace ChartBondCount
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
def halfWidth (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem mem_centredCube_iff {L : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -halfWidth L ≤ h i ∧ h i ≤ halfWidth L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset <;> assumption
theorem cellOffset_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem unitStep_top_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    (BlockAverages.unitStep F.top i : F.Cell) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem cellCentre_add_unitStep (z : F.Cell) (h : Fin 4 → ℤ) (i : Fin 4) :
    (cellCentre F.depth z + siteOfCoords F.depth h + BlockAverages.unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (h + Pi.single i 1) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem isCrossingBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) ↔
      h i = halfWidth F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff <;> assumption
def IsTreeOffset (L : ℕ) (e : (Fin 4 → ℤ) × Fin 4) : Prop :=
  e.1 e.2 ≠ halfWidth L ∧ ∀ l, e.2 < l → e.1 l = 0
theorem isAxialTreeBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) ↔
      IsTreeOffset F.blockSide (h, i) := by apply _root_.YangMills.Construction.TopLevelSites.isAxialTreeBond_iff <;> assumption
theorem zmod_cast_cast_left (P m : ℕ) (h : P = m) (a : ZMod m) :
    (((((a.cast : ℤ) : ZMod P)).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
theorem zmod_cast_intCast (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
theorem zmod_cast_cast_int (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem torusSiteInFrame_toTorusSite {m : ℕ} (j : ℕ) (hm : ∀ i, F.period j i = m) (y : F.Site j) :
    torusSiteInFrame F j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem enclosingCell_torusSiteInFrame {n : ℕ} (hs : ∀ i, F.extent i = n) (x : TorusSite (n * F.blockSide)) :
    enclosingCell (torusSiteInFrame F F.depth x) = torusSiteInFrame F F.top (parentBlock F.blockSide x) := by
  funext k
  have he : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have hlow : ∀ i, F.period F.depth i = n * F.blockSide := fun i => by simp [BlockFrame.period, hs]
  have htop : ∀ i, F.period F.top i = n := fun i => by simp [BlockFrame.period, hs]
  have h1 : siteCoords (torusSiteInFrame F F.depth x) k = ((x k).cast : ℤ) :=
    zmod_cast_cast_int _ _ (hlow k) (x k)
  show ((((siteCoords (torusSiteInFrame F F.depth x) k + ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) /
    (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ)) : ZMod (F.period F.top k)) = _
  rw [h1, he, pow_one]
  exact (zmod_cast_intCast _ _ (htop k) _).symm
theorem torusSiteInFrame_inj {F : BlockFrame} {m : ℕ} (j : ℕ) (hm : ∀ i, F.period j i = m) (x y : TorusSite m)
    (h : torusSiteInFrame F j x = torusSiteInFrame F j y) : x = y := by
  funext k
  have h1 := congrFun h k
  have e : ∀ (P : ℕ), P = m → ∀ a b : ZMod m,
      ((a.cast : ℤ) : ZMod P) = ((b.cast : ℤ) : ZMod P) → a = b := by
    intro P hP a b hab
    subst hP
    simpa using hab
  exact e _ (hm k) _ _ h1
open Classical in
theorem card_treeOffsets_dir (L : ℕ) (c : ℕ) (hc : L = c + 1) (hL : Odd L) (i : Fin 4) :
    ((centredCube L).filter fun h : Fin 4 → ℤ => h i ≠ halfWidth L ∧ ∀ l, i < l → h l = 0).card =
      L ^ (i : ℕ) * c := by
  set q := halfWidth L with hq
  obtain ⟨k, hk⟩ := hL
  have hqk : q = k := by
    simp only [hq, halfWidth, hk]
    push_cast
    omega
  let t : Fin 4 → Finset ℤ := fun l =>
    if l < i then Finset.Icc (-q) q else if l = i then Finset.Icc (-q) (q - 1) else {0}
  have hq0 : 0 ≤ q := by rw [hqk]; positivity
  have hs : ((centredCube L).filter fun h : Fin 4 → ℤ => h i ≠ q ∧ ∀ l, i < l → h l = 0) =
      Fintype.piFinset t := by
    ext h
    rw [Finset.mem_filter, _root_.YangMills.Construction.StepSettings.ChartBondCount.mem_centredCube_iff, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2, h3⟩ l
      simp only [t]
      split_ifs with a b
      · exact Finset.mem_Icc.2 (h1 l)
      · subst b
        have := h1 l
        exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · have hl : i < l := lt_of_le_of_ne (not_lt.1 a) (Ne.symm b)
        simp [h3 l hl]
    · intro h1
      refine ⟨fun l => ?_, ?_, fun l hl => ?_⟩
      · have := h1 l
        simp only [t] at this
        split_ifs at this with a b
        · exact Finset.mem_Icc.1 this
        · have := Finset.mem_Icc.1 this
          omega
        · have h2 : h l = 0 := by simpa using this
          rw [h2]
          omega
      · have := h1 i
        simp only [t, lt_irrefl, if_false, if_true] at this
        have := Finset.mem_Icc.1 this
        omega
      · have := h1 l
        simp only [t, not_lt.2 hl.le, if_false, hl.ne', if_false] at this
        simpa using this
  rw [hs, Fintype.card_piFinset]
  have e1 : (Finset.Icc (-q) q).card = L := by
    rw [Int.card_Icc, hqk, hk]
    omega
  have e2 : (Finset.Icc (-q) (q - 1)).card = c := by
    rw [Int.card_Icc, hqk]
    omega
  have e3 : ∀ l, (t l).card = if l < i then L else if l = i then c else 1 := by
    intro l
    simp only [t]
    split_ifs <;> simp [e1, e2]
  simp only [e3]
  fin_cases i <;> simp [Fin.prod_univ_four] <;> left <;> ring
open Classical in
theorem card_nonTreeOffsets_eq_card_block (hcov : BlocksCoverLowerLevel) {n : ℕ}
    [NeZero (n * F.blockSide)] (hL : Odd F.blockSide) (hn : 2 ≤ n)
    (hsn : ∀ i, F.extent i = n) (Y : TorusSite n) :
    ((((centredCube F.blockSide) ×ˢ Finset.univ).filter fun e => ¬ IsTreeOffset F.blockSide e).card : ℕ) =
      ((Finset.univ : Finset (TorusBond (n * F.blockSide))).filter fun b =>
        ¬ IsAxialTreeBond (F := F) (torusSiteInFrame F F.depth b.1, b.2) ∧
          parentBlock F.blockSide b.1 = Y).card := by
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsn]; exact hn
  have hlow : ∀ i, F.period F.depth i = n * F.blockSide := fun i => by simp [BlockFrame.period, hsn]
  have htop : ∀ i, F.period F.top i = n := fun i => by simp [BlockFrame.period, hsn]
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hc := hcov F hL hpos
  have hYc : ∃ Yc : F.Cell, Yc = torusSiteInFrame F F.top Y := ⟨_, rfl⟩
  obtain ⟨Yc, hYc⟩ := hYc
  apply Finset.card_bij (fun (e : (Fin 4 → ℤ) × Fin 4) _ =>
    ((toTorusSite (n * F.blockSide) (cellCentre F.depth Yc + siteOfCoords F.depth e.1), e.2) :
      TorusBond (n * F.blockSide)))
  · rintro ⟨h, i⟩ he
    have h2 := Finset.mem_filter.1 he
    have hh : h ∈ centredCube F.blockSide := (Finset.mem_product.1 h2.1).1
    have hback : torusSiteInFrame F F.depth
        (toTorusSite (n * F.blockSide) (cellCentre F.depth Yc + siteOfCoords F.depth h)) =
        cellCentre F.depth Yc + siteOfCoords F.depth h := torusSiteInFrame_toTorusSite _ hlow _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only
      rw [hback, isAxialTreeBond_iff hL hs2 Yc h hh i]
      exact h2.2
    · simp only
      have h3 := enclosingCell_torusSiteInFrame hsn
        (toTorusSite (n * F.blockSide) (cellCentre F.depth Yc + siteOfCoords F.depth h))
      rw [hback, enclosingCell_cellCentre_add hL hs2 Yc h hh] at h3
      exact (torusSiteInFrame_inj _ htop _ _ (hYc.symm.trans h3)).symm
  · rintro ⟨h, i⟩ he ⟨h', i'⟩ he' heq
    have hh : h ∈ centredCube F.blockSide := (Finset.mem_product.1 (Finset.mem_filter.1 he).1).1
    have hh' : h' ∈ centredCube F.blockSide := (Finset.mem_product.1 (Finset.mem_filter.1 he').1).1
    simp only [Prod.mk.injEq] at heq
    have e1 := congrArg (torusSiteInFrame F F.depth) heq.1
    rw [torusSiteInFrame_toTorusSite _ hlow, torusSiteInFrame_toTorusSite _ hlow] at e1
    have e2 := congrArg cellOffset e1
    rw [cellOffset_cellCentre_add hL hs2 Yc h hh, cellOffset_cellCentre_add hL hs2 Yc h' hh'] at e2
    rw [e2, heq.2]
  · rintro ⟨x, i⟩ hb
    have hb2 := (Finset.mem_filter.1 hb).2
    have hx := hc (torusSiteInFrame F F.depth x)
    unfold sitesOfCells at hx
    obtain ⟨z, _, hx2⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨h, hh, hxe⟩ := Finset.mem_image.1 hx2
    rw [top_sub_depth, pow_one] at hh
    have hcell : z = Yc := by
      have h3 := enclosingCell_torusSiteInFrame hsn x
      rw [← hxe, enclosingCell_cellCentre_add hL hs2 z h hh, hb2.2] at h3
      rw [h3, hYc]
    subst hcell
    refine ⟨(h, i), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩, ?_⟩, ?_⟩
    · have := hb2.1
      rw [← hxe, isAxialTreeBond_iff hL hs2 z h hh i] at this
      exact this
    · simp only [Prod.mk.injEq, and_true]
      rw [hxe]
      have h4 : ∀ i', F.period F.depth i' = n * F.blockSide := hlow
      funext k
      exact zmod_cast_cast_left _ _ (h4 k) (x k)
theorem card_centredCube_of_odd (M : ℕ) (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
open Classical in
theorem card_treeOffsets_add_one (L c : ℕ) (hc : L = c + 1) (hL : Odd L) :
    (((centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun e => IsTreeOffset L e).card + 1 =
      L ^ 4 := by
  have h1 : (((centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun e => IsTreeOffset L e).card =
      ∑ i : Fin 4, L ^ (i : ℕ) * c := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← card_treeOffsets_dir L c hc hL i, Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  rw [h1, Fin.sum_univ_four, hc]
  simp
  ring
end ChartBondCount
open ChartBondCount in
theorem chartBondCountPerBlock_holds (hcov : BlocksCoverLowerLevel) : ChartBondCountPerBlock := by
  classical
  intro L n _ _ hL hn Y
  have hnz : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have h1 := card_nonTreeOffsets_eq_card_block (F := stepBlockFrame L n) hcov hL hn (fun _ => rfl) Y
  have h2 : ((chartBonds L n).filter fun b => parentBlock L b.1 = Y) =
      (Finset.univ : Finset (TorusBond (n * L))).filter fun b =>
        ¬ IsAxialTreeBond (F := stepBlockFrame L n)
          (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).depth b.1, b.2) ∧
          parentBlock L b.1 = Y := by
    ext b
    simp [chartBonds]
    intro _
    exact Iff.rfl
  rw [h2]
  have h3 := h1.symm
  refine h3.trans ?_
  obtain ⟨c, hc⟩ : ∃ c, L = c + 1 := ⟨L - 1, by have := hL.pos; omega⟩
  have h4 := card_treeOffsets_add_one L c hc hL
  have h5 := Finset.card_filter_add_card_filter_not
    (s := (centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))) (fun e => IsTreeOffset L e)
  rw [Finset.card_product, card_centredCube_of_odd L hL] at h5
  simp only [Finset.card_univ, Fintype.card_fin] at h5
  exact show (((centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun e => ¬ IsTreeOffset L e).card =
      chartBondCount L from by
    unfold chartBondCount
    omega
end StepSettings
end YangMills.Construction
end
