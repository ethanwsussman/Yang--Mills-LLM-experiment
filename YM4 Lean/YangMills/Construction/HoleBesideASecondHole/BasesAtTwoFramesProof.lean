import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxesProof
import YangMills.Construction.HoleBesideASecondHole.BasesAtTwoFrames
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FrameTransfer
open BlockAverages LumpContours
structure SameScale (F F' : BlockFrame) : Prop where
  blockSide_eq : F.blockSide = F'.blockSide
  extent_eq : F.extent = F'.extent
variable {F F' : BlockFrame}
theorem SameScale.symm (H : SameScale F F') : SameScale F' F :=
  ⟨H.blockSide_eq.symm, H.extent_eq.symm⟩
theorem top_sub_depth (G : BlockFrame) : G.top - G.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem SameScale.period_top (H : SameScale F F') :
    ∀ k, F.period F.top k = F'.period F'.top k := by
  intro k
  simp only [BlockFrame.period, Nat.sub_self, pow_zero, H.extent_eq]
theorem SameScale.period_depth (H : SameScale F F') :
    ∀ k, F.period F.depth k = F'.period F'.depth k := by
  intro k
  simp only [BlockFrame.period, top_sub_depth, H.extent_eq, H.blockSide_eq]
theorem SameScale.top_sub_depth_eq (_ : SameScale F F') :
    F.top - F.depth = F'.top - F'.depth := by
  rw [top_sub_depth, top_sub_depth]
theorem cellCentre_transferSite (H : SameScale F F') (y : F.Cell) :
    cellCentre F'.depth (transferSite F' F'.top y) =
      transferSite F' F'.depth (cellCentre F.depth y) := by
  unfold cellCentre
  rw [siteCoords_transferSite H.period_top, transferSite_siteOfCoords H.period_depth,
    ← H.blockSide_eq, ← H.top_sub_depth_eq]
theorem enclosingCell_transferSite (H : SameScale F F') (x : F.Site F.depth) :
    enclosingCell (transferSite F' F'.depth x) = transferSite F' F'.top (enclosingCell x) := by
  unfold enclosingCell
  rw [siteCoords_transferSite H.period_depth, transferSite_siteOfCoords H.period_top,
    ← H.blockSide_eq, ← H.top_sub_depth_eq]
theorem cellBall_transferSite (H : SameScale F F') (y : F.Cell) (r : ℕ) :
    _root_.YangMills.Construction.LumpContours.cellBall (transferSite F' F'.top y) r = transferSet F' F'.top (_root_.YangMills.Construction.LumpContours.cellBall y r) := by
  unfold _root_.YangMills.Construction.LumpContours.cellBall transferSet
  rw [Finset.image_image]
  refine Finset.image_congr fun h _ => ?_
  simp only [Function.comp]
  rw [transferSite_add H.period_top, transferSite_siteOfCoords H.period_top]
theorem nearbyLumps_transferLumps (H : SameScale F F') (h : Finset (Finset (F.Site F.depth)))
    (y : F.Cell) :
    nearbyLumps (transferLumps F' F'.depth h) (transferSite F' F'.top y) =
      transferLumps F' F'.depth (nearbyLumps h y) := by
  ext l
  have hs := cutBelow_transferSet H.blockSide_eq H.period_depth H.period_top H.top_sub_depth_eq
    (_root_.YangMills.Construction.LumpContours.cellBall y 2)
  rw [mem_transferLumps H.period_depth]
  simp only [nearbyLumps, Finset.mem_filter]
  rw [mem_transferLumps H.period_depth, cellBall_transferSite H, hs,
    ← transferSet_subset_iff H.period_depth (transferSet F F.depth l)
      (cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 2)),
    transferSet_transferSet H.symm.period_depth]
theorem isCrowded_transferLumps_iff (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    IsCrowded J₀ (transferLumps F' F'.depth h) (transferSite F' F'.top y) ↔ IsCrowded J₀ h y := by
  unfold IsCrowded
  rw [nearbyLumps_transferLumps H, card_transferLumps H.period_depth]
section Boxes
variable {j j' : ℕ}
theorem isSmallBox_transferSet_iff (hL : F.blockSide = F'.blockSide)
    (h : ∀ i, F.period j i = F'.period j' i) (B : Finset (F.Site j)) :
    IsSmallBox F' (transferSet F' j' B) ↔ IsSmallBox F B := by
  constructor
  · rintro ⟨lo, hi, hb, e⟩
    exact ⟨lo, hi, fun i => by rw [hL]; exact hb i,
      transferSet_injective h (e.trans (boxSites_transfer h lo hi))⟩
  · rintro ⟨lo, hi, hb, rfl⟩
    exact ⟨lo, hi, fun i => by rw [← hL]; exact hb i, (boxSites_transfer h lo hi).symm⟩
theorem areWithin_transferSet_iff (h : ∀ i, F.period j i = F'.period j' i) (r : ℕ)
    (X Y : Finset (F.Site j)) :
    AreWithin r (transferSet F' j' X) (transferSet F' j' Y) ↔ AreWithin r X Y := by
  unfold AreWithin
  constructor
  · rintro ⟨x, hx, y, hy, hd⟩
    rw [mem_transferSet h] at hx hy
    refine ⟨_, hx, _, hy, ?_⟩
    rwa [← supDist_transferSite h, transferSite_symm h, transferSite_symm h]
  · rintro ⟨x, hx, y, hy, hd⟩
    exact ⟨_, (transferSite_mem_transferSet h X x).2 hx, _,
      (transferSite_mem_transferSet h Y y).2 hy, by rwa [supDist_transferSite h]⟩
theorem isSeparatedCover_transferLumps (hL : F.blockSide = F'.blockSide)
    (h : ∀ i, F.period j i = F'.period j' i)
    {seeds Z : Finset (Finset (F.Site j))} (hc : IsSeparatedCover seeds Z) :
    IsSeparatedCover (transferLumps F' j' seeds) (transferLumps F' j' Z) := by
  have hs : ∀ i, F'.period j' i = F.period j i := fun i => (h i).symm
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rw [mem_transferLumps h] at hB
    have := h1 _ hB
    rw [← isSmallBox_transferSet_iff hL h, transferSet_transferSet hs] at this
    exact this
  · intro l hl
    rw [mem_transferLumps h] at hl
    obtain ⟨B, hB, hsub⟩ := h2 _ hl
    refine ⟨transferSet F' j' B, (transferSet_mem_transferLumps h Z B).2 hB, ?_⟩
    rw [← transferSet_subset_iff h, transferSet_transferSet hs] at hsub
    exact hsub
  · intro B hB B' hB' hne hw
    rw [mem_transferLumps h] at hB hB'
    exact h3 _ hB _ hB' (fun e => hne (transferSet_injective hs e))
      ((areWithin_transferSet_iff hs 2 B B').2 hw)
theorem isLeastSeparatedCover_transferLumps (hL : F.blockSide = F'.blockSide)
    (h : ∀ i, F.period j i = F'.period j' i)
    {seeds Z : Finset (Finset (F.Site j))} (hc : IsLeastSeparatedCover seeds Z) :
    IsLeastSeparatedCover (transferLumps F' j' seeds) (transferLumps F' j' Z) := by
  have hs : ∀ i, F'.period j' i = F.period j i := fun i => (h i).symm
  obtain ⟨hc, hl⟩ := hc
  refine ⟨isSeparatedCover_transferLumps hL h hc, fun Z' hZ' B hB => ?_⟩
  have hb : IsSeparatedCover seeds (transferLumps F j Z') := by
    have := isSeparatedCover_transferLumps hL.symm hs hZ'
    rwa [transferLumps_transferLumps h] at this
  rw [mem_transferLumps h] at hB
  obtain ⟨B', hB', hsub⟩ := hl _ hb _ hB
  rw [mem_transferLumps hs] at hB'
  refine ⟨_, hB', ?_⟩
  rw [← transferSet_subset_iff h, transferSet_transferSet hs] at hsub
  exact hsub
theorem isLeastSeparatedCover_subset {seeds Z₁ Z₂ : Finset (Finset (F.Site j))}
    (h1 : IsLeastSeparatedCover seeds Z₁) (h2 : IsLeastSeparatedCover seeds Z₂) : Z₁ ⊆ Z₂ := by apply _root_.YangMills.Construction.BlockLocality.leastCover_subset <;> assumption
theorem mergedBoxes_transferLumps (hL : F.blockSide = F'.blockSide)
    (h : ∀ i, F.period j i = F'.period j' i) (seeds : Finset (Finset (F.Site j))) :
    mergedBoxes (transferLumps F' j' seeds) = transferLumps F' j' (mergedBoxes seeds) := by
  have hs : ∀ i, F'.period j' i = F.period j i := fun i => (h i).symm
  unfold mergedBoxes
  by_cases hex : ∃ Z, IsLeastSeparatedCover seeds Z
  · have hl := isLeastSeparatedCover_transferLumps hL h hex.choose_spec
    have hex' : ∃ Z, IsLeastSeparatedCover (transferLumps F' j' seeds) Z := ⟨_, hl⟩
    rw [dif_pos hex, dif_pos hex']
    exact Finset.Subset.antisymm (isLeastSeparatedCover_subset hex'.choose_spec hl)
      (isLeastSeparatedCover_subset hl hex'.choose_spec)
  · have hex' : ¬ ∃ Z, IsLeastSeparatedCover (transferLumps F' j' seeds) Z := by
      rintro ⟨Z, hZ⟩
      refine hex ⟨transferLumps F j Z, ?_⟩
      have := isLeastSeparatedCover_transferLumps hL.symm hs hZ
      rwa [transferLumps_transferLumps h] at this
    rw [dif_neg hex, dif_neg hex']
    simp [transferLumps]
theorem image_lumpCollar_transferLumps (h : ∀ i, F.period j i = F'.period j' i)
    (H : Finset (Finset (F.Site j))) :
    (transferLumps F' j' H).image lumpCollar = transferLumps F' j' (H.image lumpCollar) := by
  unfold transferLumps
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun l _ => ?_
  exact thicken_transferSet h _ l
theorem pathSites_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j)
    (l : List PathStep) :
    pathSites (transferSite F' j' x) l = (pathSites x l).map (transferSite F' j') := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathSites, List.map_cons]
    rw [← transferSite_stepDisplacement h, ← transferSite_add h, ih]
end Boxes
theorem excludedBoxes_transferLumps (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    excludedBoxes J₀ (transferLumps F' F'.depth h) (transferSite F' F'.top y) =
      transferLumps F' F'.depth (excludedBoxes J₀ h y) := by
  unfold excludedBoxes
  by_cases hc : IsCrowded J₀ h y
  · rw [if_pos hc, if_pos ((isCrowded_transferLumps_iff H J₀ h y).2 hc)]
    simp [transferLumps]
  · rw [if_neg hc, if_neg (mt (isCrowded_transferLumps_iff H J₀ h y).1 hc),
      nearbyLumps_transferLumps H, image_lumpCollar_transferLumps H.period_depth,
      mergedBoxes_transferLumps H.blockSide_eq H.period_depth]
theorem transferBases_apply (H : SameScale F F') (b : F.Cell → F.Site F.depth) (y : F.Cell) :
    transferBases F' b (transferSite F' F'.top y) = transferSite F' F'.depth (b y) := by
  unfold transferBases
  rw [transferSite_transferSite H.period_top]
theorem transferBases_transferBases (H : SameScale F F') (b : F.Cell → F.Site F.depth) :
    transferBases F (transferBases F' b) = b := by
  funext y
  unfold transferBases
  rw [transferSite_transferSite H.period_top, transferSite_transferSite H.period_depth]
theorem isBaseChoice_transfer (H : SameScale F F') {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    (hb : IsBaseChoice J₀ h b) :
    IsBaseChoice J₀ (transferLumps F' F'.depth h) (transferBases F' b) := by
  intro y'
  obtain ⟨y, rfl⟩ : ∃ y, y' = transferSite F' F'.top y :=
    ⟨_, (transferSite_symm H.period_top y').symm⟩
  have hcond : (nearbyLumps (transferLumps F' F'.depth h) (transferSite F' F'.top y) = ∅ ∨
      IsCrowded J₀ (transferLumps F' F'.depth h) (transferSite F' F'.top y)) ↔
      (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) := by
    rw [isCrowded_transferLumps_iff H, nearbyLumps_transferLumps H]
    simp [transferLumps]
  rw [hcond, transferBases_apply H]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [(hb y).1 hc, cellCentre_transferSite H]
  · obtain ⟨h1, h2⟩ := (hb y).2 hc
    refine ⟨?_, fun B hB x hx i e => ?_⟩
    · rw [sitesBelow_transferSite H.blockSide_eq H.period_depth H.period_top H.top_sub_depth_eq,
        transferSite_mem_transferSet H.period_depth]
      exact h1
    · rw [excludedBoxes_transferLumps H, mem_transferLumps H.period_depth] at hB
      have hx' : transferSite F F.depth x ∈ transferSet F F.depth B :=
        (transferSite_mem_transferSet H.symm.period_depth B x).2 hx
      refine h2 _ hB _ hx' i ?_
      rw [← transferSite_apply_inj H.period_depth, transferSite_symm H.period_depth]
      exact e
theorem isBaseChoice_transfer_iff (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ (transferLumps F' F'.depth h) (transferBases F' b) ↔ IsBaseChoice J₀ h b := by
  refine ⟨fun hb => ?_, isBaseChoice_transfer H⟩
  have := isBaseChoice_transfer H.symm hb
  rwa [transferLumps_transferLumps H.period_depth, transferBases_transferBases H] at this
theorem bondEnd_transferBond (H : SameScale F F') (c : F.Cell × Fin 4) :
    (transferBond F' F'.top c).1 + unitStep F'.top (transferBond F' F'.top c).2 =
      transferSite F' F'.top (c.1 + unitStep F.top c.2) := by
  simp only [transferBond]
  rw [transferSite_add H.period_top, transferSite_unitStep H.period_top]
theorem contourPath_transfer (H : SameScale F F') (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    contourPath (transferBases F' b) (transferBond F' F'.top c) ξ π = contourPath b c ξ π := by
  have off : ∀ y : F.Cell, minimalOffset (transferBases F' b (transferSite F' F'.top y))
      (cellCentre F'.depth (transferSite F' F'.top y) + siteOfCoords F'.depth ξ) =
      minimalOffset (b y) (cellCentre F.depth y + siteOfCoords F.depth ξ) := by
    intro y
    rw [transferBases_apply H, cellCentre_transferSite H,
      ← transferSite_siteOfCoords H.period_depth, ← transferSite_add H.period_depth,
      minimalOffset_transferSite H.period_depth]
  unfold contourPath
  rw [bondEnd_transferBond H]
  simp only [transferBond]
  rw [off, off, ← H.blockSide_eq]
theorem isGoodContour_transfer_iff (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4)
    (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    IsGoodContour J₀ (transferLumps F' F'.depth h) (transferBases F' b)
        (transferBond F' F'.top c) ξ π ↔
      IsGoodContour J₀ h b c ξ π := by
  unfold IsGoodContour
  rw [contourPath_transfer H, bondEnd_transferBond H]
  simp only [transferBond]
  rw [transferBases_apply H, pathSites_transferSite H.period_depth, excludedBoxes_transferLumps H,
    excludedBoxes_transferLumps H]
  constructor
  · intro hg x hx B hB hxB
    refine hg (transferSite F' F'.depth x) (List.mem_map_of_mem hx) (transferSet F' F'.depth B) ?_
      ((transferSite_mem_transferSet H.period_depth B x).2 hxB)
    rw [Finset.mem_union] at hB ⊢
    exact hB.imp (transferSet_mem_transferLumps H.period_depth _ B).2
      (transferSet_mem_transferLumps H.period_depth _ B).2
  · intro hg x' hx' B' hB' hxB'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    rw [Finset.mem_union, mem_transferLumps H.period_depth, mem_transferLumps H.period_depth,
      ← Finset.mem_union] at hB'
    exact hg x hx _ hB' ((mem_transferSet H.symm.period_depth B' x).2 hxB')
open Classical in
theorem usedContours_transfer (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4) :
    usedContours J₀ (transferLumps F' F'.depth h) (transferBases F' b) (transferBond F' F'.top c) =
      usedContours J₀ h b c := by
  have hA : allContours F' = allContours F := by
    unfold allContours
    rw [H.blockSide_eq]
  have hf : ((allContours F').filter fun e => IsGoodContour J₀ (transferLumps F' F'.depth h)
      (transferBases F' b) (transferBond F' F'.top c) e.1 e.2) =
      (allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2 := by
    rw [hA]
    exact Finset.filter_congr fun e _ => isGoodContour_transfer_iff H J₀ h b c e.1 e.2
  have c1 : IsCrowded J₀ (transferLumps F' F'.depth h) (transferBond F' F'.top c).1 ↔
      IsCrowded J₀ h c.1 :=
    isCrowded_transferLumps_iff H J₀ h c.1
  have c2 : IsCrowded J₀ (transferLumps F' F'.depth h)
      ((transferBond F' F'.top c).1 + unitStep F'.top (transferBond F' F'.top c).2) ↔
      IsCrowded J₀ h (c.1 + unitStep F.top c.2) := by
    rw [bondEnd_transferBond H]
    exact isCrowded_transferLumps_iff H J₀ h _
  unfold usedContours
  simp only [c1, c2, hf]
  rw [hA]
theorem contourMean_transfer (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    contourMean J₀ (transferLumps F' F'.depth h) (transferBases F' b)
        (transferField F' F'.depth W) (transferBond F' F'.top c) =
      contourMean J₀ h b W c := by
  unfold contourMean
  rw [usedContours_transfer H]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  rw [contourPath_transfer H]
  simp only [transferBond]
  rw [transferBases_apply H, pathHolonomy_transfer H.period_depth]
theorem contourFit_transfer (H : SameScale F F') (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) :
    contourFit J₀ (transferLumps F' F'.depth h) (transferBases F' b)
        (transferField F' F'.depth W) (transferField F' F'.top V) (transferBond F' F'.top c) =
      contourFit J₀ h b W V c := by
  unfold contourFit
  rw [contourMean_transfer H]
  simp only [transferBond]
  rw [transferField_apply H.period_top]
theorem cellOffset_transferSite (H : SameScale F F') (x : F.Site F.depth) :
    cellOffset (transferSite F' F'.depth x) = cellOffset x := by
  funext i
  unfold cellOffset
  rw [enclosingCell_transferSite H, cellCentre_transferSite H, ← transferSite_sub H.period_depth,
    valMinAbs_transferSite H.period_depth]
theorem axialGauge_transfer (H : SameScale F F') (π : Equiv.Perm (Fin 4))
    (W : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (transferField F' F'.depth W) (transferSite F' F'.depth x) = axialGauge π W x := by
  unfold axialGauge
  rw [cellOffset_transferSite H, enclosingCell_transferSite H, cellCentre_transferSite H,
    pathHolonomy_transfer H.period_depth]
theorem gaugeTransform_axialGauge_transfer (H : SameScale F F') (π : Equiv.Perm (Fin 4))
    (W : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGauge π (transferField F' F'.depth W)) (transferField F' F'.depth W)
        (transferSite F' F'.depth x) i =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGauge π W) W x i := by
  unfold _root_.YangMills.Construction.BlockAverages.gaugeTransform
  rw [axialGauge_transfer H, transferField_apply H.period_depth,
    ← transferSite_unitStep H.period_depth, ← transferSite_add H.period_depth,
    axialGauge_transfer H]
theorem isCrossingBond_transferBond_iff (H : SameScale F F') (b : F.Site F.depth × Fin 4) :
    IsCrossingBond (transferBond F' F'.depth b) ↔ IsCrossingBond b := by
  unfold IsCrossingBond
  simp only [transferBond]
  rw [← transferSite_unitStep H.period_depth, ← transferSite_add H.period_depth,
    enclosingCell_transferSite H, enclosingCell_transferSite H]
  exact (transferSite_injective H.period_top).ne_iff
theorem bondCoordinate_transfer (H : SameScale F F') (π : Equiv.Perm (Fin 4))
    (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) :
    bondCoordinate π (transferField F' F'.top V) (transferField F' F'.depth W)
        (transferBond F' F'.depth b) =
      bondCoordinate π V W b := by
  unfold bondCoordinate
  by_cases hc : IsCrossingBond b
  · rw [if_pos ((isCrossingBond_transferBond_iff H b).2 hc), if_pos hc]
    simp only [transferBond]
    rw [_root_.YangMills.Construction.FrameTransfer.gaugeTransform_axialGauge_transfer H, enclosingCell_transferSite H,
      transferField_apply H.period_top]
  · rw [if_neg (mt (isCrossingBond_transferBond_iff H b).1 hc), if_neg hc]
    simp only [transferBond]
    rw [_root_.YangMills.Construction.FrameTransfer.gaugeTransform_axialGauge_transfer H]
theorem basesAgreeAcrossFrames_holds : BasesAgreeAcrossFrames := by
  intro F F' hL hS
  have H : SameScale F F' := ⟨hL, hS⟩
  refine ⟨?_, fun S => cutBelow_transferSet H.blockSide_eq H.period_depth H.period_top
      H.top_sub_depth_eq S,
    fun S => cutBonds_transferSet H.period_top S, enclosingCell_transferSite H,
    fun J₀ h b => ⟨isBaseChoice_transfer_iff H J₀ h b, fun W c =>
      ⟨contourMean_transfer H J₀ h b W c, fun V => contourFit_transfer H J₀ h b W V c⟩⟩,
    fun π V W b => bondCoordinate_transfer H π V W b⟩
  unfold torusCells
  rw [← boxSites_transfer H.period_top, hS]
end YangMills.Construction.FrameTransfer
end
