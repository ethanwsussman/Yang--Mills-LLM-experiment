import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsAlongMoves
import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SettingFits
open YangMills.Construction YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TopLevelSites YangMills.Construction.TorusContours YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.TorusBlocks YangMills.Construction.TorusPaths YangMills.Construction.StepCosts YangMills.Construction.StepSettings YangMills.Construction.PlainAlignment YangMills.Construction.HoleSites YangMills.Construction.BlockSites
section Boxes
variable {F : BlockFrame}
theorem mergedBoxes_empty {j : ℕ} : mergedBoxes (∅ : Finset (Finset (F.Site j))) = ∅ := by
  classical
  unfold mergedBoxes
  split_ifs with hex
  · refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
    have hcov : IsSeparatedCover (∅ : Finset (Finset (F.Site j))) ∅ := ⟨by simp, by simp, by simp⟩
    obtain ⟨B', hB', -⟩ := hex.choose_spec.2 ∅ hcov B hB
    simp at hB'
  · rfl
theorem not_isCrowded_and_excludedBoxes_eq_empty {J₀ : ℕ} (hJ : 0 < J₀) {H : Finset (Finset (F.Site F.depth))}
    {y : F.Cell} (hl : nearbyLumps H y = ∅) : ¬ IsCrowded J₀ H y ∧ excludedBoxes J₀ H y = ∅ := by
  have hcr : ¬ IsCrowded J₀ H y := by
    unfold IsCrowded
    rw [hl]
    simp only [Finset.card_empty, nonpos_iff_eq_zero]
    omega
  refine ⟨hcr, ?_⟩
  unfold excludedBoxes
  rw [if_neg hcr, hl, Finset.image_empty, mergedBoxes_empty]
theorem usedContours_eq_allContours {J₀ : ℕ} (hJ : 0 < J₀) {H : Finset (Finset (F.Site F.depth))}
    (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4)
    (h1 : nearbyLumps H c.1 = ∅) (h2 : nearbyLumps H (c.1 + BlockAverages.unitStep F.top c.2) = ∅) :
    usedContours J₀ H b c = allContours F := by
  classical
  obtain ⟨c1, b1⟩ := not_isCrowded_and_excludedBoxes_eq_empty hJ h1
  obtain ⟨c2, b2⟩ := not_isCrowded_and_excludedBoxes_eq_empty hJ h2
  have hall : ((allContours F).filter fun e => IsGoodContour J₀ H b c e.1 e.2) = allContours F := by
    refine Finset.filter_true_of_mem fun e _ x _ B hB => ?_
    rw [b1, b2] at hB
    simp at hB
  unfold usedContours
  split_ifs with hcr
  · rfl
  · exact hall
theorem minimalOffset_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) :
    minimalOffset (cellCentre F.depth z) (cellCentre F.depth z + siteOfCoords F.depth ξ) = ξ := by
  have hoff := cellOffset_centre_add hL hs z ξ hξ
  unfold cellOffset at hoff
  rw [enclosingCell_centre_add hL hs z ξ hξ] at hoff
  exact hoff
theorem contourPath_eq_bondContour (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {b : F.Cell → F.Site F.depth} {c : F.Cell × Fin 4}
    (hb1 : b c.1 = cellCentre F.depth c.1)
    (hb2 : b (c.1 + BlockAverages.unitStep F.top c.2) = cellCentre F.depth (c.1 + BlockAverages.unitStep F.top c.2))
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    contourPath b c ξ π = bondContour F.blockSide ξ π c.2 := by
  unfold contourPath bondContour
  rw [hb1, hb2, minimalOffset_cellCentre_add hL hs _ hξ, minimalOffset_cellCentre_add hL hs _ hξ]
theorem axialGauge_cellCentre (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (X : F.GaugeField F.depth)
    (z : F.Cell) : axialGauge 1 X (cellCentre F.depth z) = 1 := by
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := zero_mem_centredCube hL.pos
  have e : (cellCentre F.depth z + siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = cellCentre F.depth z := by
    rw [TorusContours.siteOfCoords_zero, add_zero]
  have h1 := enclosingCell_centre_add hL hs z 0 h0
  have h2 := cellOffset_centre_add hL hs z 0 h0
  rw [e] at h1 h2
  unfold axialGauge
  rw [h1, h2]
  have hl : axisPath (0 : Fin 4 → ℤ) (1 : Equiv.Perm (Fin 4)) = [] := rfl
  rw [hl]
  rfl
theorem readAtLevel_gaugeTransform {j m : ℕ} [NeZero m] (hp : ∀ i, F.period j i = m) (g : TorusSite m → UnitQuaternion)
    (W : TorusField m) :
    readAtLevel F j (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun y => g (toTorusSite m y)) (readAtLevel F j W) := by
  funext y i
  show g (toTorusSite m y) * W (toTorusSite m y) i * (g (toTorusSite m y + TorusFields.unitStep m i))⁻¹ =
    g (toTorusSite m y) * W (toTorusSite m y) i * (g (toTorusSite m (y + BlockAverages.unitStep j i)))⁻¹
  rw [toTorusSite_add hp, toTorusSite_unitStep hp]
variable {n : ℕ} [NeZero n]
theorem toTorusSite_cellCentre (hn : ∀ i, F.extent i = n) [NeZero (n * F.blockSide)] (Y : TorusSite n) :
    toTorusSite (n * F.blockSide) (cellCentre F.depth (torusSiteInFrame F F.top Y) : F.Site F.depth) =
      blockCentreSite F.blockSide Y := by
  rw [TorusContours.cellCentre_eq]
  exact toTorusSite_refineSite hn Y
theorem contourMean_eq_plainContourAverage (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] {J₀ : ℕ} (hJ : 0 < J₀)
    {H : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} (Y : TorusSite n) (i : Fin 4)
    (W : TorusField (n * F.blockSide))
    (h1 : nearbyLumps H (torusSiteInFrame F F.top Y) = ∅)
    (h3 : nearbyLumps H (torusSiteInFrame F F.top Y + BlockAverages.unitStep F.top i) = ∅)
    (hb1 : b (torusSiteInFrame F F.top Y) = cellCentre F.depth (torusSiteInFrame F F.top Y))
    (hb2 : b (torusSiteInFrame F F.top Y + BlockAverages.unitStep F.top i) =
      cellCentre F.depth (torusSiteInFrame F F.top Y + BlockAverages.unitStep F.top i)) :
    contourMean J₀ H b (readAtLevel F F.depth W) (torusSiteInFrame F F.top Y, i) =
      plainContourAverage F.blockSide Y i W := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  unfold contourMean plainContourAverage wordAverage
  rw [usedContours_eq_allContours hJ b (torusSiteInFrame F F.top Y, i) h1 h3]
  have hw : (1 / ((allContours F).card : ℝ)) = contourWeight F.blockSide := by
    have hc : (allContours F).card = F.blockSide ^ 4 * 24 := card_contourIndex hL
    rw [hc]
    unfold contourWeight
    push_cast
    rw [mul_comm]
  rw [hw]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.mp he).1
  rw [contourPath_eq_bondContour hL hs hb1 hb2 hξ, hb1, pathHolonomy_readAtLevel (period_depth_of_extent hn),
    toTorusSite_cellCentre hn]
  rfl
theorem torusSiteInFrame_add_unitStep (hn : ∀ i, F.extent i = n) (Y : TorusSite n) (i : Fin 4) :
    torusSiteInFrame F F.top (Y + TorusFields.unitStep n i) =
      torusSiteInFrame F F.top Y + BlockAverages.unitStep F.top i := by
  apply toTorusSite_injective (period_top_of_extent hn)
  rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_add (period_top_of_extent hn),
    toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_unitStep (period_top_of_extent hn)]
theorem supDist_le_two_of_mem_cellBall (hn : ∀ i, F.extent i = n) {y y' : F.Cell} (hy : y' ∈ cellBall y 2) :
    supDist (toTorusSite n y) (toTorusSite n y') ≤ 2 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
  rw [toTorusSite_add (period_top_of_extent hn), toTorusSite_siteOfCoords (period_top_of_extent hn)]
  refine supDist_add_siteOfInt_le _ d 2 fun i => ?_
  have := TorusContours.mem_centredCube_iff.mp hd i
  norm_num at this
  omega
theorem toTorusSite_mem_plaquetteVertices {j m : ℕ} [NeZero m] (hp : ∀ i, F.period j i = m) (x₀ : F.Site j)
    (μ ν : Fin 4) {c : F.Site j} (hc : c ∈ plaquetteCorners ((x₀, μ, ν) : F.Site j × Fin 4 × Fin 4)) :
    toTorusSite m c ∈ plaquetteVertices (toTorusSite m x₀) μ ν := by
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by rw [toTorusSite_add hp, toTorusSite_unitStep hp]))
  · exact Or.inr (Or.inr (Or.inl (by rw [toTorusSite_add hp, toTorusSite_unitStep hp])))
  · exact Or.inr (Or.inr (Or.inr (by
      rw [toTorusSite_add hp, toTorusSite_add hp, toTorusSite_unitStep hp, toTorusSite_unitStep hp])))
theorem nearbyLumps_eq_empty (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n) [NeZero (n * F.blockSide)]
    {Z : Finset (TorusSite (n * F.blockSide))} (H : Finset (Finset (F.Site F.depth)))
    (hH : ∀ l ∈ H, ∃ c : F.Site F.depth, c ∈ l ∧ toTorusSite (n * F.blockSide) c ∈ Z) (Y : TorusSite n)
    (hY : ∀ z ∈ Z, 2 < supDist Y (parentBlock F.blockSide z)) : nearbyLumps H (torusSiteInFrame F F.top Y) = ∅ := by
  classical
  unfold nearbyLumps
  refine Finset.filter_eq_empty_iff.mpr fun l hl hsub => ?_
  obtain ⟨c, hc, hz⟩ := hH l hl
  have hs0 : ∀ i, 0 < F.extent i := fun i => by rw [hn]; omega
  beta_reduce at hsub
  generalize hB : cellBall (torusSiteInFrame F F.top Y) 2 = Bl at hsub
  have hcu := hsub hc
  have h3 := (mem_cutBelow_iff hL hs0).mp hcu
  rw [← hB] at h3
  have hd := supDist_le_two_of_mem_cellBall hn h3
  have hcell := enclosingCell_torusSiteInFrame hn (toTorusSite (n * F.blockSide) c)
  rw [torusSiteInFrame_toTorusSite (period_depth_of_extent hn)] at hcell
  rw [hcell, toTorusSite_torusSiteInFrame (period_top_of_extent hn),
    toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at hd
  exact absurd hd (not_le.mpr (hY _ hz))
theorem exists_base_eq_blockCentreSite_add [∀ j i, NeZero (F.period j i)] (hn : ∀ i, F.extent i = n)
    [NeZero (n * F.blockSide)] {J₀ : ℕ} {H : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    (hL1 : 1 ≤ F.blockSide) (hb : IsBaseChoice J₀ H b) (Y : TorusSite n) :
    ∃ z ∈ centredCube F.blockSide,
      toTorusSite (n * F.blockSide) (b (torusSiteInFrame F F.top Y)) = blockCentreSite F.blockSide Y + siteOfInt z := by
  obtain ⟨z, hz, hy⟩ := exists_centredCube_of_isBaseChoice hL1 hb (torusSiteInFrame F F.top Y)
  refine ⟨z, hz, ?_⟩
  rw [hy, siteAtOffset, TorusContours.toTorusSite_add (period_depth_of_extent hn),
    TorusContours.toTorusSite_siteOfCoords (period_depth_of_extent hn), toTorusSite_cellCentre hn]
theorem contourMean_eq_plainContourAverage_axialGauge [∀ j i, NeZero (F.period j i)] (hn : ∀ i, F.extent i = n)
    (hL : Odd F.blockSide) (h2 : 2 ≤ n) [NeZero (n * F.blockSide)] {J₀ : ℕ} (hJ : 0 < J₀)
    {H : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} (W₀ W : TorusField (n * F.blockSide))
    (Y : TorusSite n) (i : Fin 4)
    (h1 : nearbyLumps H (torusSiteInFrame F F.top Y) = ∅)
    (h3 : nearbyLumps H (torusSiteInFrame F F.top (Y + TorusFields.unitStep n i)) = ∅)
    (hb1 : b (torusSiteInFrame F F.top Y) = cellCentre F.depth (torusSiteInFrame F F.top Y))
    (hb2 : b (torusSiteInFrame F F.top (Y + TorusFields.unitStep n i)) =
      cellCentre F.depth (torusSiteInFrame F F.top (Y + TorusFields.unitStep n i))) :
    contourMean J₀ H b (readAtLevel F F.depth W) (torusSiteInFrame F F.top Y, i) =
      plainContourAverage F.blockSide Y i (TorusFields.gaugeTransform
        (fun x => axialGauge 1 (readAtLevel F F.depth W₀) (torusSiteInFrame F F.depth x)) W) := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hP := period_depth_of_extent hn
  have hnx := torusSiteInFrame_add_unitStep hn Y i
  rw [hnx] at h3 hb2
  set γ : TorusSite (n * F.blockSide) → UnitQuaternion :=
    fun x => axialGauge 1 (readAtLevel F F.depth W₀) (torusSiteInFrame F F.depth x) with hγ
  have hread := readAtLevel_gaugeTransform hP γ W
  have hγc : ∀ z : F.Cell, γ (toTorusSite (n * F.blockSide) (cellCentre F.depth z)) = 1 := by
    intro z
    simp only [hγ]
    rw [torusSiteInFrame_toTorusSite hP]
    exact axialGauge_cellCentre hL hs _ z
  have g := contourMean_gaugeTransform J₀ H (fun y => γ (toTorusSite (n * F.blockSide) y)) b
    (readAtLevel F F.depth W) (torusSiteInFrame F F.top Y, i)
  rw [← hread, contourMean_eq_plainContourAverage hn hL h2 hJ Y i (TorusFields.gaugeTransform γ W) h1 h3 hb1 hb2] at g
  dsimp only at g
  rw [hb1, hb2, hγc, hγc] at g
  simpa using g.symm
end Boxes
section Setting
variable {R : StepSetup} {n : ℕ} [NeZero n]
def _root_.YangMills.Construction.StepSettings.ChartSetting.nearBonds (s : ChartSetting R n) : Finset (TorusBond n) :=
  open Classical in Finset.univ.filter fun c => ∃ b ∈ s.free, supDist (parentBlock R.params.side b.1) c.1 ≤ 16
theorem stepBlockFrame_extent (R : StepSetup) (n : ℕ) : ∀ i, (stepBlockFrame R.params.side n).extent i = n :=
  fun _ => rfl
theorem stepBlockFrame_period_depth (R : StepSetup) (n : ℕ) [NeZero n] :
    ∀ i, (stepBlockFrame R.params.side n).period (stepBlockFrame R.params.side n).depth i = n * R.params.side :=
  period_depth_of_extent (stepBlockFrame_extent R n)
theorem stepBlockFrame_period_zero (R : StepSetup) (n : ℕ) [NeZero n] :
    ∀ i, (stepBlockFrame R.params.side n).period 0 i = n * R.params.side := by apply _root_.YangMills.Construction.SettingFits.stepBlockFrame_period_depth <;> assumption
instance instNeZeroStepBlockFrame (R : StepSetup) (n : ℕ) [NeZero n] :
    NeZero (n * (stepBlockFrame R.params.side n).blockSide) :=
  inferInstanceAs (NeZero (n * R.params.side))
theorem exists_mem_torusHotSites_of_mem_stepHotLumps (hfit : R.params.Admissible) (W : TorusField (n * R.params.side))
    (l : Finset ((stepBlockFrame R.params.side n).Site 0)) (hl : l ∈ stepHotLumps R.params W) :
    ∃ c : (stepBlockFrame R.params.side n).Site 0, c ∈ l ∧
      toTorusSite (n * R.params.side) c ∈ torusHotSites R.params W := by
  classical
  have hL := hfit.L_odd
  have hP0 := stepBlockFrame_period_zero R n
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨hpc, hge⟩ := Finset.mem_filter.mp hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hlp
  have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hpc).2.1
  obtain ⟨x₀, μ, ν⟩ := p
  have hcur : R.params.threshold ≤ curvature W (toTorusSite (n * R.params.side) x₀) μ ν := by
    have := plaquetteDefect_readAtLevel_eq (F := stepBlockFrame R.params.side n) (j := 0) hP0 W x₀ μ ν
    rw [← this]
    exact hge
  have hcorner := toTorusSite_mem_plaquetteVertices hP0 x₀ μ ν hc
  exact ⟨c, mem_lumpOf hL.pos hL R.params.grid c,
    mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt hcur hcorner⟩
theorem nearbyLumps_stepHotLumps_eq_empty (hfit : R.params.Admissible) (h2 : 2 ≤ n) {s : ChartSetting R n}
    (hs : s.IsAdmissible) (hR : R.IsLargeRange) {W : TorusField (n * R.params.side)}
    (hW : torusHotSites R.params W = torusHotSites R.params s.fine) {b₀ : TorusBond (n * R.params.side)}
    (hb : b₀ ∈ s.free) {Y : TorusSite n} (hY : supDist (parentBlock R.params.side b₀.1) Y ≤ 17) :
    nearbyLumps (stepHotLumps R.params W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y) = ∅ := by
  have hn := stepBlockFrame_extent R n
  have hL := hfit.L_odd
  refine nearbyLumps_eq_empty (F := stepBlockFrame R.params.side n) (Z := torusHotSites R.params s.fine) hn hL h2
    (stepHotLumps R.params W) (fun l hl => ?_) Y fun z hz => ?_
  · obtain ⟨c, hc, hz⟩ := exists_mem_torusHotSites_of_mem_stepHotLumps hfit W l hl
    exact ⟨c, hc, hW ▸ hz⟩
  · by_contra hcon
    have hd : supDist Y (parentBlock R.params.side z) ≤ 2 := not_lt.mp hcon
    have h6 := hs.far_from_support b₀ hb z (Finset.mem_union_right _ hz)
    have h7 := supDist_le_mul_supDist_parentBlock_add_one hL b₀.1 z
    have h8 := supDist_triangle (parentBlock R.params.side b₀.1) Y (parentBlock R.params.side z)
    have h9 := hR.range_large
    have h10 : supDist (parentBlock R.params.side b₀.1) (parentBlock R.params.side z) + 1 ≤ 20 := by omega
    have h11 : R.params.side * (supDist (parentBlock R.params.side b₀.1) (parentBlock R.params.side z) + 1) ≤
        R.params.side * 20 :=
      Nat.mul_le_mul_left _ h10
    omega
theorem contourMean_eq_plainContourAverage_gaugeAt (hfit : R.params.Admissible) (hJ : 0 < R.params.baseDepth)
    (h2 : 2 ≤ n) (s : ChartSetting R n) {W : TorusField (n * R.params.side)} (Y : TorusSite n) (i : Fin 4)
    (h1 : nearbyLumps (stepHotLumps R.params W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y) = ∅)
    (h3 : nearbyLumps (stepHotLumps R.params W) (torusSiteInFrame (stepBlockFrame R.params.side n)
      (stepBlockFrame R.params.side n).top (Y + TorusFields.unitStep n i)) = ∅)
    (hb1 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y) =
      cellCentre (stepBlockFrame R.params.side n).depth
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y))
    (hb2 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top
        (Y + TorusFields.unitStep n i)) =
      cellCentre (stepBlockFrame R.params.side n).depth (torusSiteInFrame (stepBlockFrame R.params.side n)
        (stepBlockFrame R.params.side n).top (Y + TorusFields.unitStep n i))) :
    contourMean R.params.baseDepth (stepHotLumps R.params W) s.bases (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y, i) =
      plainContourAverage R.params.side Y i (TorusFields.gaugeTransform (gaugeAt (R := R) s.fine) W) :=
  contourMean_eq_plainContourAverage_axialGauge (F := stepBlockFrame R.params.side n) (stepBlockFrame_extent R n)
    hfit.L_odd h2 hJ s.fine W Y i h1 h3 hb1 hb2
theorem bondFit_eq_plainAlignmentDefect (hfit : R.params.Admissible) (hJ : 0 < R.params.baseDepth) (h2 : 2 ≤ n)
    (s : ChartSetting R n) {W : TorusField (n * R.params.side)} (Y : TorusSite n) (i : Fin 4)
    (h1 : nearbyLumps (stepHotLumps R.params W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y) = ∅)
    (h3 : nearbyLumps (stepHotLumps R.params W) (torusSiteInFrame (stepBlockFrame R.params.side n)
      (stepBlockFrame R.params.side n).top (Y + TorusFields.unitStep n i)) = ∅)
    (hb1 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y) =
      cellCentre (stepBlockFrame R.params.side n).depth
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y))
    (hb2 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top
        (Y + TorusFields.unitStep n i)) =
      cellCentre (stepBlockFrame R.params.side n).depth (torusSiteInFrame (stepBlockFrame R.params.side n)
        (stepBlockFrame R.params.side n).top (Y + TorusFields.unitStep n i))) :
    bondFit R.params W s.coarse s.bases (Y, i) =
      plainAlignmentDefect R.params.side Y i (s.coarse Y i) (TorusFields.gaugeTransform (gaugeAt (R := R) s.fine) W) := by
  have hn := stepBlockFrame_extent R n
  have hm := contourMean_eq_plainContourAverage_gaugeAt hfit hJ h2 s Y i h1 h3 hb1 hb2
  have hv : readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y) i = s.coarse Y i :=
    readAtLevel_torusSiteInFrame (period_top_of_extent hn) s.coarse Y i
  unfold bondFit contourFit plainAlignmentDefect alignmentDefect
  rw [hm]
  simp only [hv]
end Setting
end YangMills.Construction.SettingFits
end
