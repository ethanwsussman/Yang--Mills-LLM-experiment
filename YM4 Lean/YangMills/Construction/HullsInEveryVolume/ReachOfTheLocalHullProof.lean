import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.FramesUnderGaugesAndTranslations
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAGround
import YangMills.Construction.HullsInEveryVolume.ReachOfTheLocalHull
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields TorusLumps StepSettings StepCosts BlockAverages LumpContours ChainNoise HullTrees WeightedResponses
  RenormalizationStepParameters ColdChain StepMarks StepReturn BlockOffsets CongruentBoxes CongruentAdmission TopLevelSites TorusContours
  BlockZones SettingShifts TorusBalls FrameLocality StepFrames
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet' {a z : TorusSite m} {Y : Finset (TorusSite m)} : z ∈ translateSet a Y ↔ z + a ∈ Y := by
  classical
  simp [translateSet]
private theorem translateSet_neg_translateSet (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet (-a) (translateSet a Y) = Y := by
  ext z
  simp [mem_translateSet']
private theorem supDist_add_add (a x y : TorusSite m) : _root_.YangMills.Construction.TorusFields.supDist (x + a) (y + a) = _root_.YangMills.Construction.TorusFields.supDist x y := by
  simp [TorusFields.supDist]
private theorem mem_thickening' {k : ℕ} {X : Finset (TorusSite m)} {z : TorusSite m} :
    z ∈ thickening k X ↔ ∃ x ∈ X, _root_.YangMills.Construction.TorusFields.supDist z x ≤ k := by
  classical
  simp [thickening]
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by
  ext z
  rw [mem_translateSet', mem_thickening', mem_thickening']
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x + a, mem_translateSet'.mp hx, by rwa [supDist_add_add]⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x - a, mem_translateSet'.mpr (by simpa using hx), ?_⟩
    rw [← supDist_add_add a]
    simpa using h
private theorem chainConnected_of_translateSet {r : ℕ} {a : TorusSite m} {Y : Finset (TorusSite m)} {z w : TorusSite m}
    (h : ChainConnected r (translateSet a Y) z w) : ChainConnected r Y (z + a) (w + a) := by
  unfold ChainConnected at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hu, hv, huv⟩ := hs
    exact ih.tail ⟨mem_translateSet'.mp hu, mem_translateSet'.mp hv, by rwa [supDist_add_add]⟩
private theorem chainConnected_translateSet_iff {r : ℕ} {a : TorusSite m} {Y : Finset (TorusSite m)} {z w : TorusSite m} :
    ChainConnected r (translateSet a Y) z w ↔ ChainConnected r Y (z + a) (w + a) := by
  refine ⟨chainConnected_of_translateSet, fun h => ?_⟩
  have h' : ChainConnected r (translateSet (-a) (translateSet a Y)) (z + a) (w + a) := by
    rw [translateSet_neg_translateSet]
    exact h
  simpa using chainConnected_of_translateSet h'
private theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by
  classical
  have key : ∀ y, translateSet a (Y.filter (ChainConnected r Y y)) =
      (translateSet a Y).filter (ChainConnected r (translateSet a Y) (y - a)) := by
    intro y
    ext z
    simp only [mem_translateSet', Finset.mem_filter, chainConnected_translateSet_iff, sub_add_cancel]
  ext X
  simp only [chainComponents, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, ⟨y + a, mem_translateSet'.mp hy, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro ⟨X₀, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y - a, mem_translateSet'.mpr (by simpa using hy), ?_⟩
    rw [key]
private def translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
private theorem mem_translateBonds {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ translateBonds a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [translateBonds]
private theorem image_fst_translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) :
    (open Classical in (translateBonds a B).image Prod.fst) =
      translateSet a (open Classical in B.image Prod.fst) := by
  classical
  ext z
  simp only [Finset.mem_image, mem_translateSet', mem_translateBonds]
  constructor
  · rintro ⟨⟨x, i⟩, h, rfl⟩
    exact ⟨_, h, rfl⟩
  · rintro ⟨⟨x, i⟩, h, e⟩
    simp only at e
    exact ⟨(z, i), by simpa [← e] using h, rfl⟩
end Sets
section Scaling
variable {n L : ℕ}
private abbrev scaled (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by
  have h : (((((x + (z : ZMod m) : ZMod m)).cast : ℤ) : ℤ) : ZMod m) = (((x.cast : ℤ) + z : ℤ) : ZMod m) := by
    push_cast
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  exact ⟨-k, by linarith⟩
private theorem parentBlock_add_scaled [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaled L v)) = parentBlock L x + siteOfInt v := by
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  funext i
  obtain ⟨k, hk⟩ := exists_cast_add_intCast (x i) ((L : ℤ) * v i)
  simp only [parentBlock, Pi.add_apply, siteOfInt]
  rw [hk]
  have e : ((x i).cast : ℤ) + (L : ℤ) * v i + ((n * L : ℕ) : ℤ) * k + ((L : ℤ) - 1) / 2 =
      (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) + (L : ℤ) * (v i + (n : ℤ) * k) := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ hL]
  push_cast
  simp
private theorem siteOfInt_scaled_neg (v : Fin 4 → ℤ) :
    (siteOfInt (scaled L (-v)) : TorusSite (n * L)) = - siteOfInt (scaled L v) := by
  funext i
  simp [siteOfInt]
private theorem siteOfInt_neg' {m : ℕ} (v : Fin 4 → ℤ) : (siteOfInt (-v) : TorusSite m) = - siteOfInt v := by
  funext i
  simp [siteOfInt]
end Scaling
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks' {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by
  classical
  simp [sitesInBlocks]
private theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) = translateSet (siteOfInt (scaled L v)) (sitesInBlocks L S) := by
  ext x
  rw [mem_translateSet', mem_sitesInBlocks', mem_sitesInBlocks', mem_translateSet', parentBlock_add_scaled]
private theorem translateSet_inter_nonempty {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔ (open Classical in (X ∩ Y).Nonempty) := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨z + a, Finset.mem_inter.mpr ⟨mem_translateSet'.mp h1, mem_translateSet'.mp h2⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨z - a, Finset.mem_inter.mpr ⟨mem_translateSet'.mpr (by simpa using h1),
      mem_translateSet'.mpr (by simpa using h2)⟩⟩
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
private theorem clusterComponents_translate :
    clusterComponents L r (translateBonds (siteOfInt (scaled L v)) bad) (translateSet (siteOfInt (scaled L v)) Yt)
        (translateSet (siteOfInt v) C) =
      (clusterComponents L r bad Yt C).image (translateSet (siteOfInt (scaled L v))) := by
  classical
  unfold clusterComponents
  rw [← chainComponents_translateSet]
  congr 1
  rw [image_fst_translateBonds, sitesInBlocks_translateSet]
  ext z
  simp [mem_translateSet']
private theorem attachedSites_translate :
    attachedSites L r (translateBonds (siteOfInt (scaled L v)) bad) (translateSet (siteOfInt (scaled L v)) Yt)
        (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt (scaled L v)) (attachedSites L r bad Yt C) := by
  classical
  ext z
  rw [mem_translateSet']
  simp only [attachedSites, Finset.mem_biUnion, Finset.mem_filter, id, clusterComponents_translate, Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨X, hX, rfl⟩, hn⟩, hz⟩
    rw [sitesInBlocks_translateSet] at hn
    exact ⟨X, ⟨hX, (translateSet_inter_nonempty _ _ _).mp (by convert hn)⟩, mem_translateSet'.mp hz⟩
  · rintro ⟨X, ⟨hX, hn⟩, hz⟩
    refine ⟨_, ⟨⟨X, hX, rfl⟩, ?_⟩, mem_translateSet'.mpr hz⟩
    rw [sitesInBlocks_translateSet]
    convert (translateSet_inter_nonempty (siteOfInt (scaled L v)) X (sitesInBlocks L C)).mpr (by convert hn)
private theorem coreBlocks_translate (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (scaled L v)) θ) = translateSet (siteOfInt v) (coreBlocks L r θ) := by
  classical
  ext y
  rw [mem_translateSet']
  simp only [coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and, thickening_translateSet]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    refine ⟨x + siteOfInt (scaled L v), Finset.mem_inter.mpr ⟨?_, mem_translateSet'.mp h2⟩⟩
    rw [mem_sitesInBlocks', parentBlock_add_scaled, Finset.mem_singleton.mp (mem_sitesInBlocks'.mp h1)]
    exact Finset.mem_singleton_self _
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    have e : parentBlock L (x + siteOfInt (scaled L (-v))) = y := by
      rw [parentBlock_add_scaled, Finset.mem_singleton.mp (mem_sitesInBlocks'.mp h1), siteOfInt_neg']
      simp
    refine ⟨x + siteOfInt (scaled L (-v)), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_sitesInBlocks', e]
      exact Finset.mem_singleton_self _
    · rw [mem_translateSet', siteOfInt_scaled_neg]
      simpa using h2
end Clusters
section HotLumps
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate' (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (_root_.YangMills.Construction.TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, _root_.YangMills.Construction.TorusFields.translate, add_right_comm x a]
private theorem mem_plaquetteVertices_add (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false, add_right_comm x a, add_left_inj,
    add_right_comm (x + TorusFields.unitStep m μ) a]
private theorem translateSet_torusLumpOf (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (z : TorusSite m) :
    translateSet (siteOfInt (scaled ℓ.side w)) (torusLumpOf ℓ (z + siteOfInt (scaled ℓ.side w))) = torusLumpOf ℓ z := by
  classical
  ext x
  rw [mem_translateSet']
  simp only [torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lumpCorner_add_side_mul hfit hLm, lumpCorner_add_side_mul hfit hLm, add_left_inj]
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotLumps ℓ (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaled ℓ.side w))) := by
  classical
  set a : TorusSite m := siteOfInt (scaled ℓ.side w) with ha
  ext l
  rw [mem_torusHotLumps_iff ℓ hfit hLm, Finset.mem_image]
  constructor
  · rintro ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩
    refine ⟨torusLumpOf ℓ (z + a), (mem_torusHotLumps_iff ℓ hfit hLm W _).mpr ⟨x + a, μ, ν, hlt, ?_, z + a, ?_, rfl⟩,
      translateSet_torusLumpOf hfit hLm w z⟩
    · rwa [← curvature_translate']
    · exact (mem_plaquetteVertices_add a x z μ ν).mp hz
  · rintro ⟨l₀, h, rfl⟩
    obtain ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLm W _).mp h
    refine ⟨x - a, μ, ν, hlt, ?_, z - a, ?_, ?_⟩
    · rw [curvature_translate', sub_add_cancel]
      exact hs
    · rw [mem_plaquetteVertices_add a, sub_add_cancel, sub_add_cancel]
      exact hz
    · have := translateSet_torusLumpOf hfit hLm w (z - a)
      rw [← ha, sub_add_cancel] at this
      exact this
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotSites ℓ (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side w)) W) =
      translateSet (siteOfInt (scaled ℓ.side w)) (torusHotSites ℓ W) := by
  classical
  ext z
  rw [mem_translateSet']
  simp only [torusHotSites, torusHotLumps_translate hfit hLm, Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hz⟩
    exact ⟨l, hl, mem_translateSet'.mp hz⟩
  · rintro ⟨l, hl, hz⟩
    exact ⟨_, ⟨l, hl, rfl⟩, mem_translateSet'.mpr hz⟩
end HotLumps
section Chart
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def cellShift : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth := fun x i => X (x + cellShift u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top := fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + cellShift u) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : linkValue (translateFine u X) x st = linkValue X (x + cellShift u) st := by
      unfold linkValue translateFine
      split_ifs
      · rfl
      · have e1 : x - BlockAverages.unitStep F.depth st.1 + cellShift u =
            x + cellShift u - BlockAverages.unitStep F.depth st.1 := by abel
        rw [e1]
    have e2 : x + stepDisplacement F.depth st + cellShift u = x + cellShift u + stepDisplacement F.depth st := by abel
    simp only [pathHolonomy, e, ih, e2]
private theorem cellCentre_add_siteOfCoords (z : F.Cell) :
    cellCentre F.depth (z + siteOfCoords F.top u) = cellCentre F.depth z + cellShift u := by
  rw [cellCentre_add F.depth (by simp [BlockFrame.top])]
  unfold cellShift
  congr 2
  funext i
  simp [BlockFrame.top]
private theorem centre_add_cellShift (z : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth z + siteOfCoords F.depth h + cellShift u =
      cellCentre F.depth (z + siteOfCoords F.top u) + siteOfCoords F.depth h := by
  rw [cellCentre_add_siteOfCoords]
  abel
private theorem enclosingCell_add_cellShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    enclosingCell (x + cellShift u) = enclosingCell x + siteOfCoords F.top u := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [centre_add_cellShift, TopLevelSites.enclosingCell_centre_add hL hs _ _ hh,
    TopLevelSites.enclosingCell_centre_add hL hs _ _ hh]
private theorem cellOffset_add_cellShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    cellOffset (x + cellShift u) = cellOffset x := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [centre_add_cellShift, TopLevelSites.cellOffset_centre_add hL hs _ _ hh,
    TopLevelSites.cellOffset_centre_add hL hs _ _ hh]
private theorem isCrossingBond_add_cellShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) (i : Fin 4) :
    IsCrossingBond (x + cellShift u, i) ↔ IsCrossingBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [centre_add_cellShift, TopLevelSites.isCrossingBond_iff hL hs _ _ hh, TopLevelSites.isCrossingBond_iff hL hs _ _ hh]
private theorem isAxialTreeBond_add_cellShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) (i : Fin 4) :
    IsAxialTreeBond (x + cellShift u, i) ↔ IsAxialTreeBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [centre_add_cellShift, TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh,
    TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh]
private theorem axialGauge_translateFine (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + cellShift u) := by
  unfold axialGauge
  rw [pathHolonomy_translateFine, cellOffset_add_cellShift u hL hs, enclosingCell_add_cellShift u hL hs,
    cellCentre_add_siteOfCoords]
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4))
    (U : F.GaugeField F.top) (X : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) = bondCoordinate π U X (x + cellShift u, i) := by
  classical
  have e : gaugeTransform (axialGauge π (translateFine u X)) (translateFine u X) x i =
      gaugeTransform (axialGauge π X) X (x + cellShift u) i := by
    unfold BlockAverages.gaugeTransform
    rw [axialGauge_translateFine u hL hs, axialGauge_translateFine u hL hs]
    have e2 : x + BlockAverages.unitStep F.depth i + cellShift u =
        x + cellShift u + BlockAverages.unitStep F.depth i := by abel
    simp only [translateFine, e2]
  unfold bondCoordinate
  by_cases h : IsCrossingBond (x, i)
  · have h' : IsCrossingBond (x + cellShift u, i) := (isCrossingBond_add_cellShift u hL hs x i).mpr h
    rw [if_pos h, if_pos h']
    simp only [e, translateCoarse, enclosingCell_add_cellShift u hL hs]
  · have h' : ¬ IsCrossingBond (x + cellShift u, i) := fun c => h ((isCrossingBond_add_cellShift u hL hs x i).mp c)
    rw [if_neg h, if_neg h']
    simp only [e]
end Chart
section StepFrame
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem cellShift_stepFrame (v : Fin 4 → ℤ) :
    (cellShift (F := stepBlockFrame ℓ.side n) v : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
        (siteOfInt (scaled ℓ.side v) : TorusSite (n * ℓ.side)) :=
  (TopLevelSites.torusSiteInFrame_siteOfInt (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) stepBlockFrame_period_zero (scaled ℓ.side v)).symm
private theorem torusSiteInFrame_add_scaled (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side)) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (x + siteOfInt (scaled ℓ.side v)) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x +
        cellShift (F := stepBlockFrame ℓ.side n) v := by
  rw [cellShift_stepFrame]
  exact TopLevelSites.torusSiteInFrame_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) stepBlockFrame_period_zero _ _
private theorem toTorusSite_add_cellShift (v : Fin 4 → ℤ) (x : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) :
    toTorusSite (n * ℓ.side) (x + cellShift (F := stepBlockFrame ℓ.side n) v) =
      toTorusSite (n * ℓ.side) x + siteOfInt (scaled ℓ.side v) := by
  rw [TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) stepBlockFrame_period_zero]
  congr 1
  exact TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) stepBlockFrame_period_zero _
private theorem toTorusSite_add_siteOfCoords (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by
  rw [TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) (N := n)
    _root_.YangMills.Construction.TorusContours.stepBlockFrame_period_one]
  congr 1
  exact TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top)
    (N := n) _root_.YangMills.Construction.TorusContours.stepBlockFrame_period_one _
private theorem readAtLevel_zero_translate (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) :
    readAtLevel (stepBlockFrame ℓ.side n) 0 (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side v)) W) =
      translateFine (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 0 W) := by
  funext x i
  exact congrArg (fun z => W z i) (toTorusSite_add_cellShift v x).symm
private theorem readAtLevel_one_translate (v : Fin 4 → ℤ) (V : TorusField n) :
    readAtLevel (stepBlockFrame ℓ.side n) 1 (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) =
      translateCoarse (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by
  funext y i
  exact congrArg (fun z => V z i) (toTorusSite_add_siteOfCoords v y).symm
private theorem two_le_extent (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (scaled ℓ.side v), i) := by
  unfold chartCoord
  rw [readAtLevel_zero_translate, readAtLevel_one_translate]
  refine (bondCoordinate_translate (F := stepBlockFrame ℓ.side n) v hL (two_le_extent hn) _ _ _ _ i).trans ?_
  exact congrArg (fun s : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth =>
    bondCoordinate (F := stepBlockFrame ℓ.side n) 1 (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
      (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (s, i)) (torusSiteInFrame_add_scaled v x).symm
private theorem mem_chartBonds_add_scaled (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side))
    (i : Fin 4) :
    (x + siteOfInt (scaled ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by
  classical
  simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
  show ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (x + siteOfInt (scaled ℓ.side v)), i) ↔
    ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x, i)
  rw [torusSiteInFrame_add_scaled]
  exact not_congr (isAxialTreeBond_add_cellShift (F := stepBlockFrame ℓ.side n) v hL (two_le_extent hn) _ i)
end StepFrame
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markedBonds_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) :
    markedBonds R (translateSet (siteOfInt v) C) =
      translateBonds (siteOfInt (scaled R.params.side v)) (markedBonds R C) := by
  classical
  ext ⟨x, i⟩
  rw [mem_translateBonds]
  simp only [markedBonds, Finset.mem_filter, mem_translateSet']
  rw [mem_chartBonds_add_scaled hL hn, parentBlock_add_scaled]
private theorem bondMark_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (x + siteOfInt (scaled R.params.side v), i)) :
    bondMark R (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (scaled R.params.side v), i) := by
  unfold bondMark
  rw [chartCoord_translate hL hn, h]
end Marks
section Depth
variable {n : ℕ} [NeZero n]
private def IsDeepIn (m : ℕ) (c : Finset (TorusSite n)) (v : TorusSite n) : Prop :=
  v ∈ c ∧ ∀ w, w ∉ c → m ≤ _root_.YangMills.Construction.TorusFields.supDist v w
private theorem isDeepIn_mono {A B : ℕ} (h : A ≤ B) {c : Finset (TorusSite n)} {v : TorusSite n}
    (hv : IsDeepIn B c v) : IsDeepIn A c v :=
  ⟨hv.1, fun w hw => h.trans (hv.2 w hw)⟩
private theorem isDeepIn_of_near {A d : ℕ} (hA : 0 < A) {c : Finset (TorusSite n)} {z u : TorusSite n}
    (hz : IsDeepIn (A + d) c z) (h : _root_.YangMills.Construction.TorusFields.supDist u z ≤ d) : IsDeepIn A c u := by
  have key : ∀ w, w ∉ c → A ≤ _root_.YangMills.Construction.TorusFields.supDist u w := by
    intro w hw
    have h1 := hz.2 w hw
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z u w
    have h3 : _root_.YangMills.Construction.TorusFields.supDist z u = _root_.YangMills.Construction.TorusFields.supDist u z := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    omega
  refine ⟨?_, key⟩
  by_contra hu
  have := key u hu
  rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
  omega
private def AgreeDeepIn (c : Finset (TorusSite n)) (W W' : TorusField n) : Prop :=
  ∀ b : TorusBond n, IsDeepIn 8 c b.1 → IsDeepIn 8 c (b.1 + TorusFields.unitStep n b.2) → W b.1 b.2 = W' b.1 b.2
private theorem AgreeDeepIn.symm {c : Finset (TorusSite n)} {W W' : TorusField n} (h : AgreeDeepIn c W W') :
    AgreeDeepIn c W' W := fun b h1 h2 => (h b h1 h2).symm
private theorem isDeepIn_bond {c : Finset (TorusSite n)} {u : TorusSite n} (hu : IsDeepIn 9 c u) (i : Fin 4) :
    IsDeepIn 8 c u ∧ IsDeepIn 8 c (u + TorusFields.unitStep n i) := by
  refine ⟨isDeepIn_mono (by norm_num) hu, isDeepIn_of_near (A := 8) (d := 1) (by norm_num) hu ?_⟩
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le u i
end Depth
section Blocks
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem isDeepIn_sitesInBlocks {A B : ℕ} (hAB : B ≤ (A - 1) * L) (hA : 1 ≤ A) {c : Finset (TorusSite n)}
    {v : TorusSite (n * L)} (h : IsDeepIn A c (parentBlock L v)) : IsDeepIn B (sitesInBlocks L c) v := by
  refine ⟨mem_sitesInBlocks'.2 h.1, fun w hw => ?_⟩
  have h1 := h.2 _ (fun hc => hw (mem_sitesInBlocks'.2 hc))
  have h2 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one L v w
  have h3 : A - 1 ≤ _root_.YangMills.Construction.TorusFields.supDist v w / L := by omega
  have h4 := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne L))).1 h3
  omega
private theorem agreeAbove_box (hL : 8 ≤ L) {c : Finset (TorusSite n)} {W W' : TorusField (n * L)}
    (h : AgreeDeepIn (sitesInBlocks L c) W W') {y : TorusSite n} (hy : IsDeepIn 8 c y) {m : ℕ} (hm : m ≤ 4) :
    AgreeAbove L (HullTrees.box y m) W W' := by
  have key : ∀ v : TorusSite (n * L), parentBlock L v ∈ HullTrees.box y m → IsDeepIn 8 (sitesInBlocks L c) v := by
    intro v hv
    obtain ⟨y', hy', hd⟩ := mem_thickening'.1 hv
    rw [Finset.mem_singleton.1 hy'] at hd
    refine isDeepIn_sitesInBlocks (A := 4) ?_ (by norm_num) (isDeepIn_of_near (d := 4) (by norm_num) hy (by omega))
    omega
  intro b h1 h2
  exact h b (key _ h1) (key _ h2)
end Blocks
section Fields
variable {ℓ : StepParameters}
private theorem agreeDeepIn_stepOutcome (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hL : 8 ≤ ℓ.side) (s n : ℕ) [NeZero n] {c : Finset (TorusSite n)} {W W' : TorusField (n * ℓ.side)}
    {ξ ξ' : StepNoise ℓ n} (hW : AgreeDeepIn (sitesInBlocks ℓ.side c) W W')
    (hb : ∀ y ∈ c, ξ.1 y = ξ'.1 y) (hc : ∀ b : TorusBond n, b.1 ∈ c → ξ.2.1 b = ξ'.2.1 b) :
    AgreeDeepIn c (rule.stepOutcome T s n W ξ).2.1 (rule.stepOutcome T s n W' ξ').2.1 := by
  intro b h1 h2
  have hbase : ∀ y, IsDeepIn 8 c y → rule.base s n W y (ξ.1 y) = rule.base s n W' y (ξ'.1 y) := by
    intro y hy
    rw [hb y hy.1]
    exact hr.base_depends s n W W' y _ (agreeAbove_box hL hW hy (by norm_num))
  show rule.value s n W (fun y => rule.base s n W y (ξ.1 y)) (b.1, b.2) (ξ.2.1 (b.1, b.2)) =
    rule.value s n W' (fun y => rule.base s n W' y (ξ'.1 y)) (b.1, b.2) (ξ'.2.1 (b.1, b.2))
  rw [show ξ.2.1 (b.1, b.2) = ξ'.2.1 (b.1, b.2) from hc _ h1.1]
  exact hr.value_depends s n W W' _ _ (b.1, b.2) _ (agreeAbove_box hL hW h1 (by norm_num)) (hbase _ h1) (hbase _ h2)
private theorem agreeDeepIn_topField (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hL : 8 ≤ ℓ.side) :
    ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (W W' : TorusField (fineSide ℓ.side s n))
      (U U' : ChainNoise ℓ s n),
      (∀ b : TorusBond (fineSide ℓ.side s n), b.1 ∈ sitesUnder ℓ.side s n c →
        b.1 + TorusFields.unitStep (fineSide ℓ.side s n) b.2 ∈ sitesUnder ℓ.side s n c → W b.1 b.2 = W' b.1 b.2) →
      NoiseAgreeAbove ℓ s n c U U' →
      AgreeDeepIn c (topField ℓ s n (rule.chain T s n W U)) (topField ℓ s n (rule.chain T s n W' U')) := by
  intro s
  induction s with
  | zero =>
    intro n _ c W W' U U' hW _ b h1 h2
    exact hW b h1.1 h2.1
  | succ s ih =>
    intro n _ c W W' U U' hW hU
    obtain ⟨h0, hb, hc, -⟩ := hU
    exact agreeDeepIn_stepOutcome rule T hr hL s n
      (ih (n * ℓ.side) (sitesInBlocks ℓ.side c) W W' U.1 U'.1 hW h0) hb hc
end Fields
section Seam
private theorem natAbs_valMinAbs_cast_sub_le {P m L : ℕ} [NeZero m] (hP : 0 < P) (h1 : P ≤ m) (h2 : m ≤ P + L)
    (a b : ZMod P) (e : ℤ) (h : a - b = (e : ZMod P)) :
    ((((ZMod.cast a : ℤ) : ZMod m) - ((ZMod.cast b : ℤ) : ZMod m)).valMinAbs).natAbs ≤ e.natAbs + L := by
  have : NeZero P := ⟨hP.ne'⟩
  set d : ℤ := (a - b).valMinAbs with hd
  have hde : d.natAbs ≤ e.natAbs := by
    rw [hd, h]
    exact _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le e
  have hdP : d.natAbs ≤ P / 2 := ZMod.natAbs_valMinAbs_le _
  have hdc : ((d : ℤ) : ZMod P) = a - b := ZMod.coe_valMinAbs _
  set A : ℤ := (ZMod.cast a : ℤ) with hA
  set B : ℤ := (ZMod.cast b : ℤ) with hB
  have hAc : ((A : ℤ) : ZMod P) = a := ZMod.intCast_zmod_cast a
  have hBc : ((B : ℤ) : ZMod P) = b := ZMod.intCast_zmod_cast b
  have hA0 : 0 ≤ A ∧ A < P := by
    have e1 : A = ((a.val : ℕ) : ℤ) := ZMod.cast_eq_val a
    have e2 := ZMod.val_lt a
    omega
  have hB0 : 0 ≤ B ∧ B < P := by
    have e1 : B = ((b.val : ℕ) : ℤ) := ZMod.cast_eq_val b
    have e2 := ZMod.val_lt b
    omega
  have hdvd : (P : ℤ) ∣ d - (A - B) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hAc, hBc, hdc]
  obtain ⟨t, ht⟩ := hdvd
  have hd2 : 2 * d ≤ P ∧ -(P : ℤ) ≤ 2 * d := by omega
  have ht1 : t = -1 ∨ t = 0 ∨ t = 1 := by
    have u1 : t < 2 := by
      by_contra hc
      have : (2 : ℤ) ≤ t := by omega
      nlinarith
    have u2 : -2 < t := by
      by_contra hc
      have : t ≤ -2 := by omega
      nlinarith
    omega
  have hcast : ((A : ℤ) : ZMod m) - ((B : ℤ) : ZMod m) = ((d + ((m : ℤ) - P) * t : ℤ) : ZMod m) := by
    rw [← Int.cast_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨t, ?_⟩
    linarith
  rw [hcast]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  rcases ht1 with rfl | rfl | rfl <;> simp only [mul_neg, mul_one, mul_zero] <;> omega
private theorem supDist_toTorusSite_le {F : BlockFrame} {j m L : ℕ} [NeZero m] (hpos : ∀ i, 0 < F.period j i)
    (h1 : ∀ i, F.period j i ≤ m) (h2 : ∀ i, m ≤ F.period j i + L) (x y : F.Site j) (E : ℕ)
    (h : ∀ i, ∃ e : ℤ, x i - y i = (e : ZMod (F.period j i)) ∧ e.natAbs ≤ E) :
    _root_.YangMills.Construction.TorusFields.supDist (toTorusSite m x) (toTorusSite m y) ≤ E + L := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  obtain ⟨e, he, hE⟩ := h i
  exact (natAbs_valMinAbs_cast_sub_le (hpos i) (h1 i) (h2 i) _ _ e he).trans (by omega)
private theorem plaquetteHolonomy_eq {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (a : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (a, μ, ν) =
      X a μ * (X (a + BlockAverages.unitStep j μ) ν *
        ((X (a + BlockAverages.unitStep j ν) μ)⁻¹ * (X a ν)⁻¹)) := by
  have a1 : a + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν - BlockAverages.unitStep j μ =
      a + BlockAverages.unitStep j ν := by abel
  have a2 : a + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν + -BlockAverages.unitStep j μ -
      BlockAverages.unitStep j ν = a := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    mul_one, a1, a2]
private theorem single_one_bounds (μ i : Fin 4) :
    0 ≤ (Pi.single μ 1 : Fin 4 → ℤ) i ∧ (Pi.single μ 1 : Fin 4 → ℤ) i ≤ 1 := by
  by_cases h : i = μ
  · subst h
    simp
  · simp [h]
private theorem exists_of_mem_plaquetteCorners {F : BlockFrame} {j : ℕ} {a q : F.Site j} {μ ν : Fin 4}
    (h : q ∈ plaquetteCorners (a, μ, ν)) :
    ∃ A : Fin 4 → ℤ, q = a + siteOfCoords j A ∧ ∀ i, 0 ≤ A i ∧ A i ≤ 2 := by
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; simp [siteOfCoords], fun i => by simp⟩
  · exact ⟨Pi.single μ 1, rfl, fun i => by have := single_one_bounds μ i; omega⟩
  · exact ⟨Pi.single ν 1, rfl, fun i => by have := single_one_bounds ν i; omega⟩
  · refine ⟨Pi.single μ 1 + Pi.single ν 1, ?_, fun i => ?_⟩
    · funext i
      simp [siteOfCoords, BlockAverages.unitStep, add_assoc]
    · have := single_one_bounds μ i
      have := single_one_bounds ν i
      simp only [Pi.add_apply]
      omega
private theorem exists_of_mem_lumpOf {L : ℕ} (hL : Odd L) (g : LumpGrid L) {F : BlockFrame} {j : ℕ} {x y : F.Site j}
    (hy : y ∈ lumpOf g x) :
    ∀ i, ∃ e : ℤ, y i - x i = (e : ZMod (F.period j i)) ∧ e.natAbs ≤ 2 ^ 15 := by
  unfold lumpOf boxSites at hy
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hy
  intro i
  have hi : siteCoords x i - offsetFromCentre L (siteCoords x i) + g.lower (offsetFromCentre L (siteCoords x i)) ≤ H i ∧
      H i ≤ siteCoords x i - offsetFromCentre L (siteCoords x i) + g.upper (offsetFromCentre L (siteCoords x i)) :=
    Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hH i)
  refine ⟨H i - siteCoords x i, ?_, ?_⟩
  · have e1 : ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := ZMod.intCast_zmod_cast (x i)
    simp only [siteOfCoords]
    push_cast
    rw [e1]
  · obtain ⟨h, hh⟩ := hL
    have hLz : (L : ℤ) = 2 * h + 1 := by subst hh; push_cast; ring
    have hhalf : ((L : ℤ) - 1) / 2 = h := by rw [hLz]; omega
    set c := siteCoords x i with hc
    have hoff : offsetFromCentre L c = (c + h) % (L : ℤ) - h := by
      unfold offsetFromCentre
      rw [hhalf]
    set o := offsetFromCentre L c with ho
    have hm0 := Int.emod_nonneg (c + h) (show (L : ℤ) ≠ 0 by omega)
    have hm1 := Int.emod_lt_of_pos (c + h) (show (0 : ℤ) < L by omega)
    have hobd : |o| ≤ ((L : ℤ) - 1) / 2 := by
      rw [hhalf, abs_le]
      constructor <;> omega
    obtain ⟨-, b2, b3, -⟩ := g.mem_interval o hobd
    obtain ⟨-, s2⟩ := g.interval_length o hobd
    norm_num at s2 ⊢
    omega
end Seam
section HotSites
private theorem mem_torusHotSites_of_agree (ℓ : StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    (W W' : TorusField m) (z : TorusSite m)
    (hag : ∀ u i, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 2 ^ 15 + 2 + ℓ.side → W u i = W' u i) (hz : z ∈ torusHotSites ℓ W) :
    z ∈ torusHotSites ℓ W' := by
  classical
  simp only [torusHotSites, torusHotLumps, hotLumps, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    id_eq] at hz ⊢
  obtain ⟨l, ⟨l₀, ⟨⟨a, μ, ν⟩, ⟨hp, hs⟩, x, hx, rfl⟩, rfl⟩, hzl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hzl
  refine ⟨_, ⟨_, ⟨(a, μ, ν), ⟨hp, ?_⟩, x, hx, rfl⟩, rfl⟩, Finset.mem_image.2 ⟨y, hy, rfl⟩⟩
  have hLpos : 0 < ℓ.side := hL.pos
  have hposi : ∀ i, 0 < (stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i := by
    have ha : a ∈ levelSites (stepBlockFrame ℓ.side (m / ℓ.side)) 0 := by
      unfold cutPlaquettes at hp
      exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
    unfold levelSites boxSites at ha
    obtain ⟨H, hH, -⟩ := Finset.mem_image.1 ha
    intro i
    have hi : (0 : ℤ) ≤ H i ∧ H i ≤ ((stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i : ℤ) - 1 :=
      Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hH i)
    omega
  have hp1 : ∀ i, (stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i ≤ m := fun i => by
    rw [period_zero]
    exact Nat.div_mul_le_self m ℓ.side
  have hp2 : ∀ i, m ≤ (stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i + ℓ.side := fun i => by
    rw [period_zero]
    have e1 := Nat.div_add_mod m ℓ.side
    have e2 := Nat.mod_lt m hLpos
    rw [mul_comm] at e1
    omega
  have hr : ∀ q ∈ plaquetteCorners ((a, μ, ν) : (stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4), ∀ i,
      readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W q i =
        readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W' q i := by
    intro q hq i
    show W (toTorusSite m q) i = W' (toTorusSite m q) i
    refine hag _ i ?_
    obtain ⟨A, hqA, hA⟩ := exists_of_mem_plaquetteCorners hq
    obtain ⟨A', hxA, hA'⟩ := exists_of_mem_plaquetteCorners hx
    refine supDist_toTorusSite_le hposi hp1 hp2 q y (2 ^ 15 + 2) fun k => ?_
    obtain ⟨e, he, hE⟩ := exists_of_mem_lumpOf hL ℓ.grid hy k
    refine ⟨A k - A' k - e, ?_, ?_⟩
    · rw [hxA] at he
      rw [hqA]
      simp only [Pi.add_apply, siteOfCoords] at he ⊢
      push_cast
      rw [← he]
      ring
    · have b1 := hA k
      have b2 := hA' k
      norm_num at hE ⊢
      omega
  have hsame : plaquetteHolonomy (readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W) (a, μ, ν) =
      plaquetteHolonomy (readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W') (a, μ, ν) := by
    have c1 : a ∈ plaquetteCorners ((a, μ, ν) : (stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [plaquetteCorners]
    have c2 : a + BlockAverages.unitStep 0 μ ∈
        plaquetteCorners ((a, μ, ν) : (stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [plaquetteCorners]
    have c3 : a + BlockAverages.unitStep 0 ν ∈
        plaquetteCorners ((a, μ, ν) : (stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [plaquetteCorners]
    rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq, hr a c1 μ, hr a c1 ν, hr _ c2 ν, hr _ c3 μ]
  have hc : plaquetteDefect (readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W) (a, μ, ν) =
      plaquetteDefect (readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W') (a, μ, ν) := by
    unfold plaquetteDefect
    rw [hsame]
  rw [← hc]
  exact hs
private theorem mem_torusHotSites_iff_of_deep (ℓ : StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    {c : Finset (TorusSite m)} {W W' : TorusField m} (h : AgreeDeepIn c W W') {r : ℕ}
    (hr : 2 ^ 15 + 2 + ℓ.side + 9 ≤ r) {z : TorusSite m} (hz : IsDeepIn r c z) :
    z ∈ torusHotSites ℓ W ↔ z ∈ torusHotSites ℓ W' := by
  have one : ∀ {W W' : TorusField m}, AgreeDeepIn c W W' → z ∈ torusHotSites ℓ W → z ∈ torusHotSites ℓ W' := by
    intro W W' h
    refine mem_torusHotSites_of_agree ℓ hL W W' z fun u i hu => ?_
    have hu9 : IsDeepIn 9 c u := isDeepIn_of_near (by norm_num) (isDeepIn_mono (by omega) hz) hu
    have h2 := isDeepIn_bond hu9 i
    exact h (u, i) h2.1 h2.2
  exact ⟨one h, one h.symm⟩
private theorem mem_thickening_hotSites_iff_of_deep (ℓ : StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    {c : Finset (TorusSite m)} {W W' : TorusField m} (h : AgreeDeepIn c W W') {r : ℕ}
    (hr : 2 ^ 15 + 2 + ℓ.side + 9 ≤ r) {z : TorusSite m} (hz : IsDeepIn (4 * r) c z) :
    z ∈ thickening (2 * r) (torusHotSites ℓ W) ↔ z ∈ thickening (2 * r) (torusHotSites ℓ W') := by
  have one : ∀ {W W' : TorusField m}, AgreeDeepIn c W W' →
      z ∈ thickening (2 * r) (torusHotSites ℓ W) → z ∈ thickening (2 * r) (torusHotSites ℓ W') := by
    intro W W' h hz'
    obtain ⟨x, hx, hd⟩ := mem_thickening'.1 hz'
    have hx' : IsDeepIn (2 * r) c x :=
      isDeepIn_of_near (d := 2 * r) (by omega) (isDeepIn_mono (by omega) hz) (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact hd)
    exact mem_thickening'.2 ⟨x, (mem_torusHotSites_iff_of_deep ℓ hL h hr (isDeepIn_mono (by omega) hx')).1 hx, hd⟩
  exact ⟨one h, one h.symm⟩
end HotSites
section Coins
private theorem siteAtOffset_eq_add {F : BlockFrame} (c : F.Cell) (a b : Fin 4 → ℤ) :
    (siteAtOffset c a : F.Site F.depth) = siteAtOffset c b + siteOfCoords F.depth (a - b) := by
  have e : (siteOfCoords F.depth a : F.Site F.depth) = siteOfCoords F.depth b + siteOfCoords F.depth (a - b) := by
    funext i
    simp [siteOfCoords]
  unfold siteAtOffset
  rw [e, add_assoc]
private theorem chartCoord_eq_of_agree (hblocks : BlockDataIsLocal) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    {n : ℕ} [NeZero n] {V V' : TorusField n} {W W' : TorusField (n * ℓ.side)} (b : TorusBond (n * ℓ.side))
    (h16 : 16 ≤ n)
    (hV1 : V (parentBlock ℓ.side b.1) b.2 = V' (parentBlock ℓ.side b.1) b.2)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, (e j).natAbs ≤ 4 * ℓ.side) →
      W (b.1 + siteOfInt e) k = W' (b.1 + siteOfInt e) k) :
    chartCoord ℓ V W b = chartCoord ℓ V' W' b := by
  set w := parentBlock ℓ.side b.1 with hw
  set o := siteOffset (L := ℓ.side) b.1 with ho
  have hb : blockSite w o = b.1 := blockSite_parentBlock_siteOffset b.1
  have c₁ : torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1 =
      siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) (refinedOffset ℓ.side 0 o) := by
    have e := torusSiteInFrame_blockSite (n := n) (L := ℓ.side) 0 w o
    rw [hb] at e
    exact e
  have hp : ∀ i, (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side := fun i => period_zero i
  have on_near : ∀ u : Fin 4 → ℤ,
      toTorusSite (n * ℓ.side) (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u :
        (stepBlockFrame ℓ.side n).Site 0) = b.1 + siteOfInt (u - refinedOffset ℓ.side 0 o) := by
    intro u
    have a1 : toTorusSite (n * ℓ.side) (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w)
        (refinedOffset ℓ.side 0 o) : (stepBlockFrame ℓ.side n).Site 0) = b.1 :=
      (congrArg (toTorusSite (n * ℓ.side)) c₁).symm.trans (TopLevelSites.toTorusSite_torusSiteInFrame hp b.1)
    have a2 := TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := 0) hp
      (u - refinedOffset ℓ.side 0 o)
    have a3 := TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := 0) hp
      (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) (refinedOffset ℓ.side 0 o))
      (siteOfCoords 0 (u - refinedOffset ℓ.side 0 o))
    exact (congrArg (toTorusSite (n * ℓ.side))
        (siteAtOffset_eq_add (F := stepBlockFrame ℓ.side n) _ u (refinedOffset ℓ.side 0 o))).trans
      (a3.trans (congrArg₂ (· + ·) a1 a2))
  have hag : ∀ (u : Fin 4 → ℤ) (k : Fin 4), TorusFields.OffsetInBox (3 * ℓ.side) u →
      TorusFields.OffsetInBox (3 * ℓ.side) (u + Pi.single k 1) →
      readAtLevel (stepBlockFrame ℓ.side n) 0 W (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u) k =
        readAtLevel (stepBlockFrame ℓ.side n) 0 W' (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u) k := by
    intro u k hu _
    show W (toTorusSite (n * ℓ.side) (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u :
        (stepBlockFrame ℓ.side n).Site 0)) k =
      W' (toTorusSite (n * ℓ.side) (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u :
        (stepBlockFrame ℓ.side n).Site 0)) k
    rw [on_near]
    refine hW _ k fun j => ?_
    have h1 := abs_le.1 (hu j)
    have h2 := (BlockOffsets.mem_centredCube_iff _).1 (refinedOffset_mem_centredCube hfit.L_odd o) j
    push_cast at h1
    simp only [Pi.sub_apply]
    omega
  have hVr : readAtLevel (stepBlockFrame ℓ.side n) 1 V (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) b.2 =
      readAtLevel (stepBlockFrame ℓ.side n) 1 V' (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) b.2 := by
    rw [TopLevelSites.readAtLevel_torusSiteInFrame (fun i => period_one i),
      TopLevelSites.readAtLevel_torusSiteInFrame (fun i => period_one i)]
    exact hV1
  have key := (hblocks ℓ hfit n n h16 h16 _ _ _ _ hag).2 _ _ _ b.2 (refinedOffset_mem_centredCube hfit.L_odd o) hVr
  unfold chartCoord
  rw [c₁]
  exact key
private theorem bondMark_eq_of_agree (hframe : FrameCoordLocal) (hblocks : BlockDataIsLocal)
    {R : StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n] {V V' : TorusField n}
    {W W' : TorusField (n * R.params.side)}
    (b : TorusBond (n * R.params.side)) (h16 : 16 ≤ n) (hm : 0 < R.frameReach) (hm2 : 4 * R.frameReach + 5 < n)
    (hV : FieldsAgreeNear V V' (parentBlock R.params.side b.1) (parentBlock R.params.side b.1) R.frameReach)
    (hV1 : V (parentBlock R.params.side b.1) b.2 = V' (parentBlock R.params.side b.1) b.2)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, (e j).natAbs ≤ 4 * R.params.side) →
      W (b.1 + siteOfInt e) k = W' (b.1 + siteOfInt e) k) :
    bondMark R V W b = bondMark R V' W' b := by
  have hf := hframe R.params R.anchorRadius R.depth R.frameReach n n V V' b b hfit hm hm2 hm2 rfl rfl hV
  have hc := chartCoord_eq_of_agree hblocks hfit b h16 hV1 hW
  unfold bondMark
  rw [hc, hf]
variable {ℓ : StepParameters}
open Classical in
private theorem mem_stepOutcome_bonds (rule : NoiseRule ℓ) (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (W : TorusField (n * ℓ.side)) (ξ : StepNoise ℓ n) (b : TorusBond (n * ℓ.side)) :
    b ∈ (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W ξ).2.2) ↔
      b ∈ markedBonds (T.stage s).toStepSetup
          (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n W ξ).2.1) ∧
        ¬ ((ξ.2.2 b : ℝ) < bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n W ξ).2.1 W b) := by
  unfold NoiseRule.stepOutcome
  exact Finset.mem_filter
private theorem bondMark_eq_of_deep (hframe : FrameCoordLocal) (hblocks : BlockDataIsLocal)
    {R : StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n] {c : Finset (TorusSite n)} {V V' : TorusField n}
    {W W' : TorusField (n * R.params.side)} (b : TorusBond (n * R.params.side))
    (hw : AgreeDeepIn (sitesInBlocks R.params.side c) W W') (hv : AgreeDeepIn c V V') (h16 : 16 ≤ n)
    (hm : 0 < R.frameReach) (hm2 : 4 * R.frameReach + 5 < n) {D : ℕ} (hD : R.frameReach + 9 ≤ D)
    (hy : IsDeepIn D c (parentBlock R.params.side b.1)) :
    bondMark R V W b = bondMark R V' W' b := by
  have hL : 8 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  refine bondMark_eq_of_agree hframe hblocks hfit b h16 hm hm2 ?_ ?_ ?_
  · intro e he
    have h1 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1 + siteOfInt e.1) (parentBlock R.params.side b.1) ≤ R.frameReach := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
      have := abs_le.1 (he.1 i)
      omega
    have hu9 : IsDeepIn 9 c (parentBlock R.params.side b.1 + siteOfInt e.1) :=
      isDeepIn_of_near (d := R.frameReach) (by norm_num) (isDeepIn_mono (by omega) hy) h1
    have h2 := isDeepIn_bond hu9 e.2
    exact hv (parentBlock R.params.side b.1 + siteOfInt e.1, e.2) h2.1 h2.2
  · have hy9 : IsDeepIn 9 c (parentBlock R.params.side b.1) := isDeepIn_mono (by omega) hy
    have h2 := isDeepIn_bond hy9 b.2
    exact hv (parentBlock R.params.side b.1, b.2) h2.1 h2.2
  · intro e k he
    have hv0 : _root_.YangMills.Construction.TorusFields.supDist (b.1 + siteOfInt e) b.1 ≤ 4 * R.params.side := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ he
    have hbl : ∀ u : TorusSite (n * R.params.side), _root_.YangMills.Construction.TorusFields.supDist u b.1 ≤ 4 * R.params.side + 1 →
        IsDeepIn 2 c (parentBlock R.params.side u) := by
      intro u hu
      have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side u b.1
      have h2 : _root_.YangMills.Construction.TorusFields.supDist u b.1 / R.params.side ≤ 4 := by
        apply Nat.lt_succ_iff.1
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      exact isDeepIn_of_near (d := 5) (by norm_num) (isDeepIn_mono (by omega) hy) (by omega)
    have hv1 : _root_.YangMills.Construction.TorusFields.supDist (b.1 + siteOfInt e + TorusFields.unitStep _ k) b.1 ≤ 4 * R.params.side + 1 := by
      have e1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (b.1 + siteOfInt e + TorusFields.unitStep _ k) (b.1 + siteOfInt e) b.1
      have e2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (b.1 + siteOfInt e) k
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at e2
      omega
    exact hw (b.1 + siteOfInt e, k)
      (isDeepIn_sitesInBlocks (A := 2) (by omega) (by norm_num) (hbl (b.1 + siteOfInt e) (by omega)))
      (isDeepIn_sitesInBlocks (A := 2) (by omega) (by norm_num) (hbl _ hv1))
private theorem le_clusterRange {x : ℝ} {N : ℕ} (h : (N : ℝ) ^ 100 ≤ x) : N ≤ clusterRange x := by
  have h1 : (N : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    calc (N : ℝ) = ((N : ℝ) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
      _ ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) h (by norm_num)
  exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
private theorem clusterRange_le_succ {x x' B : ℝ} (hB : 1 ≤ B) (hx' : B ^ 100 ≤ x') (hx : 0 ≤ x)
    (h : x ≤ x' + 2 * B) : clusterRange x ≤ clusterRange x' + 1 := by
  have hx0 : 0 ≤ x' := le_trans (by positivity) hx'
  set b : ℝ := x' ^ ((1 : ℝ) / 100) with hb
  have hb100 : b ^ 100 = x' := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hBb : B ≤ b := by
    calc B = (B ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
      _ ≤ b := Real.rpow_le_rpow (by positivity) hx' (by norm_num)
  have h1 : b ^ 99 ≤ (b + 1) ^ 99 := pow_le_pow_left₀ (by linarith) (by linarith) _
  have h2 : (b + 1) ^ 2 ≤ (b + 1) ^ 99 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : b ^ 99 * b ≤ (b + 1) ^ 99 * b := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : x ≤ (b + 1) ^ 100 := by
    have e2 : b ^ 100 = b ^ 99 * b := by ring
    nlinarith
  have h5 : x ^ ((1 : ℝ) / 100) ≤ b + 1 := by
    calc x ^ ((1 : ℝ) / 100) ≤ ((b + 1) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx h4 (by norm_num)
      _ = b + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
  unfold clusterRange
  calc ⌈x ^ ((1 : ℝ) / 100)⌉₊ ≤ ⌈b + 1⌉₊ := Nat.ceil_mono h5
    _ = ⌈b⌉₊ + 1 := Nat.ceil_add_one (by linarith)
end Coins
section Reads
variable {ℓ : StepParameters}
open Classical in
private def hullStep (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n]
    (lo : Finset (TorusSite (n * ℓ.side)) × (TorusSite (n * ℓ.side) → ℝ))
    (bad : Finset (TorusBond (n * ℓ.side))) (C Q : Finset (TorusSite n)) : Finset (TorusSite n) × (TorusSite n → ℝ) :=
  let R := (T.stage j).toStepSetup
  let Z := C ∪ (coreBlocks ℓ.side R.range (attachedSites ℓ.side R.range bad lo.1 C) ∩ Q)
  let Y := thickening (R.nextRange / 2) Z ∩ Q
  (Y, fun y => if y ∈ Z then s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ lo.1, lo.2 z else if y ∈ Y then s₁ else 0)
open Classical in
private theorem localHullData_succ (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n)) :
    localHullData T s₁ (j + 1) n w Q =
      hullStep T s₁ j n (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q))
        ((show Finset (TorusBond (n * ℓ.side)) from w.2.2.2).filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q)
        (hotCoreSites (T.stage j).toStepSetup w.2.2.1 ∩ Q) Q := by
  simp only [localHullData, hullStep]
private theorem exists_parentBlock_eq {n L : ℕ} [NeZero n] [NeZero L] (w : TorusSite n) :
    ∃ x : TorusSite (n * L), parentBlock L x = w := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨0 + siteOfInt (scaled L fun i => ((w i).cast : ℤ)), ?_⟩
  rw [parentBlock_add_scaled]
  have h0 : parentBlock L (0 : TorusSite (n * L)) = 0 := by
    funext i
    have e : (((L : ℤ) - 1) / 2) / (L : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    simp [parentBlock, e]
  rw [h0, zero_add]
  funext i
  exact ZMod.intCast_zmod_cast (w i)
private theorem localHullData_eq_of_agree (hframe : FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T) (hfit : ℓ.Admissible) (s₁ : ℝ) (u : ℕ)
    (hbig : ∀ j ≤ u, 2 ^ 16 + ℓ.side ≤ stageRange T j)
    (hnear : ∀ j < u, stageRange T j ≤ stageRange T (j + 1) + 1) :
    ∀ (s : ℕ), s ≤ u → ∀ (n : ℕ) [NeZero n] (c Q : Finset (TorusSite n)) (W W' : TorusField (fineSide ℓ.side s n))
      (U U' : ChainNoise ℓ s n),
      (∀ b : TorusBond (fineSide ℓ.side s n), b.1 ∈ sitesUnder ℓ.side s n c →
        b.1 + TorusFields.unitStep (fineSide ℓ.side s n) b.2 ∈ sitesUnder ℓ.side s n c → W b.1 b.2 = W' b.1 b.2) →
      NoiseAgreeAbove ℓ s n c U U' → (∀ v ∈ Q, IsDeepIn (5 * stageRange T s) c v) → (∃ w, w ∉ c) →
      localHullData T s₁ s n (rule.chain T s n W U) Q = localHullData T s₁ s n (rule.chain T s n W' U') Q := by
  classical
  have hL : 8 ≤ ℓ.side := by
    have := hfit.L_ge
    omega
  have hodd := hfit.L_odd
  intro s
  induction s with
  | zero =>
    intro _ n _ c Q W W' U U' hW hU hQ _
    have hd := agreeDeepIn_topField rule T hr hL 0 n c W W' U U' hW hU
    have hb := hbig 0 (Nat.zero_le _)
    have key : hullSet T 0 n (rule.chain T 0 n W U) ∩ Q = hullSet T 0 n (rule.chain T 0 n W' U') ∩ Q := by
      ext z
      simp only [Finset.mem_inter]
      refine and_congr_left fun hz => ?_
      exact mem_thickening_hotSites_iff_of_deep ℓ hodd hd (r := stageRange T 0) (by omega)
        (isDeepIn_mono (by omega) (hQ z hz))
    simp only [localHullData, key]
  | succ s ih =>
    intro hs n _ c Q W W' U U' hW hU hQ hoff
    have hU' := hU
    obtain ⟨h0, hb, hc, hk⟩ := hU
    have hbs := hbig s (by omega)
    have hbs' := hbig (s + 1) hs
    have hns := hnear s (by omega)
    have hWd := agreeDeepIn_topField rule T hr hL s (n * ℓ.side) (sitesInBlocks ℓ.side c) W W' U.1 U'.1 hW h0
    have hVd := agreeDeepIn_topField rule T hr hL (s + 1) n c W W' U U' hW hU'
    have hlo : localHullData T s₁ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1) (sitesInBlocks ℓ.side Q) =
        localHullData T s₁ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W' U'.1) (sitesInBlocks ℓ.side Q) := by
      refine ih (by omega) (n * ℓ.side) (sitesInBlocks ℓ.side c) (sitesInBlocks ℓ.side Q) W W' U.1 U'.1 hW h0 ?_ ?_
      · intro v hv
        refine isDeepIn_sitesInBlocks (A := 5 * stageRange T (s + 1)) ?_ (by omega)
          (hQ _ (mem_sitesInBlocks'.1 hv))
        have h2 : (5 * stageRange T (s + 1) - 1) * 2 ≤ (5 * stageRange T (s + 1) - 1) * ℓ.side :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      · obtain ⟨w, hw⟩ := hoff
        obtain ⟨x, hx⟩ := exists_parentBlock_eq (L := ℓ.side) w
        exact ⟨x, fun hc' => hw (hx ▸ mem_sitesInBlocks'.1 hc')⟩
    set w₁ := rule.chain T (s + 1) n W U with hw₁
    set w₂ := rule.chain T (s + 1) n W' U' with hw₂
    have hC : hotCoreSites (T.stage s).toStepSetup w₁.2.2.1 ∩ Q = hotCoreSites (T.stage s).toStepSetup w₂.2.2.1 ∩ Q := by
      ext z
      simp only [Finset.mem_inter]
      refine and_congr_left fun hz => ?_
      exact mem_thickening_hotSites_iff_of_deep ℓ hodd hVd (r := stageRange T (s + 1)) (by omega)
        (isDeepIn_mono (by omega) (hQ z hz))
    have hbad : (show Finset (TorusBond (n * ℓ.side)) from w₁.2.2.2).filter (fun b => b.1 ∈ sitesInBlocks ℓ.side Q) =
        (show Finset (TorusBond (n * ℓ.side)) from w₂.2.2.2).filter (fun b => b.1 ∈ sitesInBlocks ℓ.side Q) := by
      ext b
      refine Finset.mem_filter.trans (Iff.trans ?_ Finset.mem_filter.symm)
      refine and_congr_left fun hbq => ?_
      have hy := hQ _ (mem_sitesInBlocks'.1 hbq)
      obtain ⟨w, hw⟩ := hoff
      have h1 := hy.2 w hw
      have h2 := two_mul_supDist_le (parentBlock ℓ.side b.1) w
      have e0 : (T.stage s).toStepSetup.range = stageRange T s := rfl
      have e2 : (T.stage s).toStepSetup.frameReach = stageRange T s / 2 ^ 11 := rfl
      have hm0 : 0 < (T.stage s).toStepSetup.frameReach := by
        rw [e2]
        omega
      have hm2 : 4 * (T.stage s).toStepSetup.frameReach + 5 < n := by
        rw [e2]
        omega
      have h16 : 16 ≤ n := by omega
      have hD : (T.stage s).toStepSetup.frameReach + 9 ≤ 5 * stageRange T (s + 1) := by
        rw [e2]
        omega
      have hmark := bondMark_eq_of_deep hframe hblocks (R := (T.stage s).toStepSetup) hfit b hWd hVd h16 hm0 hm2 hD hy
      have hnoise := hk b (mem_sitesInBlocks'.1 hbq |> fun h => (hy.1))
      have hbl : parentBlock ℓ.side b.1 ∈ hotCoreSites (T.stage s).toStepSetup w₁.2.2.1 ↔
          parentBlock ℓ.side b.1 ∈ hotCoreSites (T.stage s).toStepSetup w₂.2.2.1 :=
        mem_thickening_hotSites_iff_of_deep ℓ hodd hVd (r := stageRange T (s + 1)) (by omega)
          (isDeepIn_mono (by omega) hy)
      have hm : ∀ C C' : Finset (TorusSite n), (parentBlock ℓ.side b.1 ∈ C ↔ parentBlock ℓ.side b.1 ∈ C') →
          (b ∈ markedBonds (T.stage s).toStepSetup C ↔ b ∈ markedBonds (T.stage s).toStepSetup C') := by
        intro C C' h
        simp only [markedBonds, Finset.mem_filter, h]
      have e1 := mem_stepOutcome_bonds rule T s n
        (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1)) U.2 b
      have e2' := mem_stepOutcome_bonds rule T s n
        (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W' U'.1)) U'.2 b
      refine e1.trans (Iff.trans ?_ e2'.symm)
      refine and_congr (hm _ _ hbl) ?_
      rw [hnoise]
      exact not_congr (iff_of_eq (congrArg (fun t : ℝ => ((U'.2.2.2 b : unitInterval) : ℝ) < t) hmark))
    rw [localHullData_succ, localHullData_succ]
    show hullStep T s₁ s n (localHullData T s₁ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1)
        (sitesInBlocks ℓ.side Q)) _ _ Q =
      hullStep T s₁ s n (localHullData T s₁ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W' U'.1)
        (sitesInBlocks ℓ.side Q)) _ _ Q
    rw [hlo, hbad, hC]
private theorem mem_sitesUnder_of_forall (L : ℕ) [NeZero L] : ∀ (u n : ℕ) [NeZero n] (c : Finset (TorusSite n)),
    (∀ x, x ∈ c) → ∀ x, x ∈ sitesUnder L u n c := by
  intro u
  induction u with
  | zero => intro n _ c h x; exact h x
  | succ u ih =>
    intro n _ c h x
    exact ih (n * L) (sitesInBlocks L c) (fun y => mem_sitesInBlocks'.2 (h _)) x
private theorem eq_of_noiseAgreeAbove_univ : ∀ (u n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (U U' : ChainNoise ℓ u n),
    (∀ x, x ∈ c) → NoiseAgreeAbove ℓ u n c U U' → U = U' := by
  intro u
  induction u with
  | zero => intro n _ c U U' _ _; rfl
  | succ u ih =>
    intro n _ c U U' h hU
    obtain ⟨h0, hb, hc, hk⟩ := hU
    refine Prod.ext (ih (n * ℓ.side) (sitesInBlocks ℓ.side c) U.1 U'.1 (fun y => mem_sitesInBlocks'.2 (h _)) h0)
      (Prod.ext (funext fun y => hb y (h y)) (Prod.ext (funext fun b => hc b (h _))
        (funext fun b => hk b (mem_sitesInBlocks'.2 (h _) |> mem_sitesInBlocks'.1))))
end Reads
section Translates
variable {ℓ : StepParameters}
private def IsTranslateOf (ℓ : StepParameters) :
    (s n : ℕ) → [NeZero n] → (Fin 4 → ℤ) → MarkedSample ℓ s n → MarkedSample ℓ s n → Prop
  | 0, n, _, v, w, w' => (show TorusField n from w') = _root_.YangMills.Construction.TorusFields.translate (siteOfInt v) (show TorusField n from w)
  | s + 1, n, _, v, w, w' => IsTranslateOf ℓ s (n * ℓ.side) (scaled ℓ.side v) w.1 w'.1 ∧
      w'.2.2.1 = _root_.YangMills.Construction.TorusFields.translate (siteOfInt v) w.2.2.1 ∧
      (show Finset (TorusBond (n * ℓ.side)) from w'.2.2.2) =
        translateBonds (siteOfInt (scaled ℓ.side v)) (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2)
private theorem IsTranslateOf.topField_eq {s n : ℕ} [NeZero n] {v : Fin 4 → ℤ} {w w' : MarkedSample ℓ s n}
    (h : IsTranslateOf ℓ s n v w w') : topField ℓ s n w' = _root_.YangMills.Construction.TorusFields.translate (siteOfInt v) (topField ℓ s n w) := by
  cases s with
  | zero => exact h
  | succ s => exact h.2.1
private theorem isBlockTorusSide_mul {n : ℕ} (hB : IsBlockTorusSide ℓ n) (h0 : 0 < ℓ.side) :
    IsBlockTorusSide ℓ (n * ℓ.side) := by
  refine ⟨Dvd.dvd.mul_right hB.1 _, ?_⟩
  have h1 := hB.2
  have h2 : ℓ.n₀ ≤ n := by
    have : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ h0
    omega
  calc ℓ.side * ℓ.n₀ = ℓ.n₀ * ℓ.side := Nat.mul_comm _ _
    _ ≤ n * ℓ.side := Nat.mul_le_mul_right _ h2
private theorem hotCoreSites_translate (hfit : ℓ.Admissible) (R : StepSetup) (hR : R.params = ℓ) {n : ℕ} [NeZero n]
    (hLn : ℓ.side ∣ n) (w : Fin 4 → ℤ) (V : TorusField n) :
    hotCoreSites R (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled R.params.side w)) V) =
      translateSet (siteOfInt (scaled R.params.side w)) (hotCoreSites R V) := by
  subst hR
  unfold hotCoreSites
  rw [torusHotSites_translate hfit hLn, thickening_translateSet]
private theorem stepOutcome_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (s n : ℕ) [NeZero n]
    (hLn : ℓ.side ∣ n) (h2 : 2 ≤ n) (w : Fin 4 → ℤ) (X : TorusField (n * ℓ.side)) (ξ : StepNoise ℓ n)
    (hfr : ∀ (V : TorusField n) (u : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (_root_.YangMills.Construction.TorusFields.translate (siteOfInt u) V) (c.1 - siteOfInt (scaled ℓ.side u), c.2) =
        frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c) :
    (rule.stepOutcome T s n (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side (scaled ℓ.side w))) X)
        (fun y => ξ.1 (y + siteOfInt (scaled ℓ.side w)), fun c => ξ.2.1 (c.1 + siteOfInt (scaled ℓ.side w), c.2),
          fun b => ξ.2.2 (b.1 + siteOfInt (scaled ℓ.side (scaled ℓ.side w)), b.2))).2.1 =
      _root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side w)) (rule.stepOutcome T s n X ξ).2.1 ∧
    (show Finset (TorusBond (n * ℓ.side)) from
        (rule.stepOutcome T s n (_root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side (scaled ℓ.side w))) X)
        (fun y => ξ.1 (y + siteOfInt (scaled ℓ.side w)), fun c => ξ.2.1 (c.1 + siteOfInt (scaled ℓ.side w), c.2),
          fun b => ξ.2.2 (b.1 + siteOfInt (scaled ℓ.side (scaled ℓ.side w)), b.2))).2.2) =
      translateBonds (siteOfInt (scaled ℓ.side (scaled ℓ.side w)))
        (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n X ξ).2.2) := by
  classical
  set v : Fin 4 → ℤ := scaled ℓ.side w with hv
  set ξ' : StepNoise ℓ n := (fun y => ξ.1 (y + siteOfInt v), fun c => ξ.2.1 (c.1 + siteOfInt v, c.2),
    fun b => ξ.2.2 (b.1 + siteOfInt (scaled ℓ.side v), b.2)) with hξ'
  set X' : TorusField (n * ℓ.side) := _root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side v)) X with hX'
  have hV : (rule.stepOutcome T s n X' ξ').2.1 = _root_.YangMills.Construction.TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n X ξ).2.1 := by
    funext y i
    have ho : (fun y => rule.base s n X' y (ξ'.1 y)) =
        fun y => (fun y => rule.base s n X y (ξ.1 y)) (y + siteOfInt v) := by
      funext y
      exact hr.base_translate s n X v y _
    show rule.value s n X' (fun y => rule.base s n X' y (ξ'.1 y)) (y, i) (ξ.2.1 (y + siteOfInt v, i)) =
      rule.value s n X (fun y => rule.base s n X y (ξ.1 y)) (y + siteOfInt v, i) (ξ.2.1 (y + siteOfInt v, i))
    rw [ho]
    exact hr.value_translate s n X (fun y => rule.base s n X y (ξ.1 y)) v (y, i) _
  refine ⟨hV, ?_⟩
  ext ⟨x, i⟩
  rw [mem_translateBonds, mem_stepOutcome_bonds, mem_stepOutcome_bonds, hV]
  have hm : markedBonds (T.stage s).toStepSetup
        (hotCoreSites (T.stage s).toStepSetup (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n X ξ).2.1)) =
      translateBonds (siteOfInt (scaled ℓ.side v)) (markedBonds (T.stage s).toStepSetup
        (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n X ξ).2.1)) := by
    rw [hv, hotCoreSites_translate hfit (T.stage s).toStepSetup rfl hLn w]
    exact markedBonds_translate hfit.L_odd h2 _ _
  rw [hm, mem_translateBonds]
  refine and_congr_right fun hc => ?_
  have hf := hfr (rule.stepOutcome T s n X ξ).2.1 v _ hc
  simp only [add_sub_cancel_right] at hf
  have hk := bondMark_translate (R := (T.stage s).toStepSetup) hfit.L_odd h2 v (rule.stepOutcome T s n X ξ).2.1 X x i hf
  show ¬ ((ξ.2.2 (x + siteOfInt (scaled ℓ.side v), i) : ℝ) < bondMark (T.stage s).toStepSetup _ _ (x, i)) ↔ _
  rw [hk]
private theorem chain_isTranslateOf (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (u : ℕ)
    (hfr : ∀ s < u, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (V : TorusField n) (v : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaled ℓ.side v), c.2) =
        frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c) :
    ∀ (s : ℕ), s ≤ u → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ)
      (p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n),
      IsTranslateOf ℓ s n (scaled ℓ.side w) (rule.chain T s n p.1 p.2)
        (rule.chain T s n (pairTranslate ℓ s n (scaled ℓ.side w) p).1 (pairTranslate ℓ s n (scaled ℓ.side w) p).2) := by
  have hL0 : 0 < ℓ.side := hfit.L_odd.pos
  intro s
  induction s with
  | zero =>
    intro _ n _ _ w p
    show _root_.YangMills.Construction.TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ 0 * scaled ℓ.side w i) p.1 =
      _root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side w)) p.1
    simp only [pow_zero, one_mul]
  | succ s ih =>
    intro hs n _ hB w p
    have hI := ih (by omega) (n * ℓ.side) (isBlockTorusSide_mul hB hL0) (scaled ℓ.side w) (p.1, p.2.1)
    have hshift : (fun i => (ℓ.side : ℤ) ^ (s + 1) * scaled ℓ.side w i) =
        fun i => (ℓ.side : ℤ) ^ s * scaled ℓ.side (scaled ℓ.side w) i := by
      funext i
      simp only [scaled]
      ring
    have hp : (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).1 =
        (pairTranslate ℓ s (n * ℓ.side) (scaled ℓ.side (scaled ℓ.side w)) (p.1, p.2.1)).1 := by
      show _root_.YangMills.Construction.TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (s + 1) * scaled ℓ.side w i) p.1 = _
      rw [hshift]
      rfl
    have hq : (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.1 =
        (pairTranslate ℓ s (n * ℓ.side) (scaled ℓ.side (scaled ℓ.side w)) (p.1, p.2.1)).2 := rfl
    have hn : 2 ≤ n := by
      have h1 := hB.2
      have h2 : ℓ.side * 1 ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_left _ (by have := hfit.n₀_ge; omega)
      have := hfit.L_ge
      omega
    have hstep := stepOutcome_translate rule T hr hfit s n hB.1 hn w
      (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) p.1 p.2.1)) p.2.2
      (fun V v c hc => hfr s (by omega) n hB V v c hc)
    have htop := IsTranslateOf.topField_eq hI
    refine ⟨?_, ?_, ?_⟩
    · show IsTranslateOf ℓ s (n * ℓ.side) (scaled ℓ.side (scaled ℓ.side w)) (rule.chain T s (n * ℓ.side) p.1 p.2.1)
        (rule.chain T s (n * ℓ.side) (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).1
          (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.1)
      rw [hp, hq]
      exact hI
    · show (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
          (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).1 (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.1))
          (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.2).2.1 = _
      rw [hp, hq, htop]
      exact hstep.1
    · show (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side)
          (rule.chain T s (n * ℓ.side) (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).1
            (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.1))
          (pairTranslate ℓ (s + 1) n (scaled ℓ.side w) p).2.2).2.2) = _
      rw [hp, hq, htop]
      exact hstep.2
open Classical in
private theorem hullStep_translate (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (v : Fin 4 → ℤ)
    (lo : Finset (TorusSite (n * ℓ.side)) × (TorusSite (n * ℓ.side) → ℝ)) (bad : Finset (TorusBond (n * ℓ.side)))
    (C Q : Finset (TorusSite n)) :
    hullStep T s₁ j n (translateSet (siteOfInt (scaled ℓ.side v)) lo.1,
        fun z => lo.2 (z + siteOfInt (scaled ℓ.side v)))
        (translateBonds (siteOfInt (scaled ℓ.side v)) bad) (translateSet (siteOfInt v) C) (translateSet (siteOfInt v) Q) =
      (translateSet (siteOfInt v) (hullStep T s₁ j n lo bad C Q).1,
        fun y => (hullStep T s₁ j n lo bad C Q).2 (y + siteOfInt v)) := by
  have hZ : ∀ r : ℕ, translateSet (siteOfInt v) C ∪ (coreBlocks ℓ.side r (attachedSites ℓ.side r
        (translateBonds (siteOfInt (scaled ℓ.side v)) bad) (translateSet (siteOfInt (scaled ℓ.side v)) lo.1)
        (translateSet (siteOfInt v) C)) ∩ translateSet (siteOfInt v) Q) =
      translateSet (siteOfInt v) (C ∪ (coreBlocks ℓ.side r (attachedSites ℓ.side r bad lo.1 C) ∩ Q)) := by
    intro r
    rw [attachedSites_translate, coreBlocks_translate]
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, mem_translateSet']
  have hY : ∀ (r' : ℕ) (Z : Finset (TorusSite n)),
      thickening (r' / 2) (translateSet (siteOfInt v) Z) ∩ translateSet (siteOfInt v) Q =
        translateSet (siteOfInt v) (thickening (r' / 2) Z ∩ Q) := by
    intro r' Z
    rw [thickening_translateSet]
    ext z
    simp only [Finset.mem_inter, mem_translateSet']
  simp only [hullStep]
  rw [hZ, hY]
  refine Prod.ext rfl ?_
  funext y
  simp only [mem_translateSet']
  by_cases h1 : y + siteOfInt v ∈ C ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
      (attachedSites ℓ.side (T.stage j).toStepSetup.range bad lo.1 C) ∩ Q)
  · simp only [if_pos h1]
    congr 1
    refine Finset.sum_nbij' (fun z : TorusSite (n * ℓ.side) => z + siteOfInt (scaled ℓ.side v))
      (fun z : TorusSite (n * ℓ.side) => z - siteOfInt (scaled ℓ.side v)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨e1, e2⟩ := Finset.mem_inter.1 hz
      refine Finset.mem_inter.2 ⟨?_, mem_translateSet'.1 e2⟩
      rw [mem_sitesInBlocks', parentBlock_add_scaled, Finset.mem_singleton.1 (mem_sitesInBlocks'.1 e1)]
      exact Finset.mem_singleton_self _
    · intro z hz
      obtain ⟨e1, e2⟩ := Finset.mem_inter.1 hz
      refine Finset.mem_inter.2 ⟨?_, mem_translateSet'.2 (by simpa using e2)⟩
      have e3 : parentBlock ℓ.side (z - siteOfInt (scaled ℓ.side v)) + siteOfInt v = parentBlock ℓ.side z := by
        rw [← parentBlock_add_scaled]
        simp
      rw [mem_sitesInBlocks', Finset.mem_singleton]
      have e4 := Finset.mem_singleton.1 (mem_sitesInBlocks'.1 e1)
      rw [e4] at e3
      exact add_right_cancel e3
    · intro z _
      simp
    · intro z _
      simp
    · intro z _
      rfl
  · simp only [if_neg h1]
private theorem localHullData_translate (T : StageTower ℓ) (hfit : ℓ.Admissible) (s₁ : ℝ) :
    ∀ (s n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ) (d d' : MarkedSample ℓ s n)
      (Q : Finset (TorusSite n)),
      IsTranslateOf ℓ s n (scaled ℓ.side w) d d' →
      localHullData T s₁ s n d' (translateSet (siteOfInt (scaled ℓ.side w)) Q) =
        (translateSet (siteOfInt (scaled ℓ.side w)) (localHullData T s₁ s n d Q).1,
          fun y => (localHullData T s₁ s n d Q).2 (y + siteOfInt (scaled ℓ.side w))) := by
  classical
  have hL0 : 0 < ℓ.side := hfit.L_odd.pos
  intro s
  induction s with
  | zero =>
    intro n _ hB w d d' Q h
    have hh : hullSet T 0 n d' = translateSet (siteOfInt (scaled ℓ.side w)) (hullSet T 0 n d) := by
      show thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ (show TorusField n from d')) =
        translateSet (siteOfInt (scaled ℓ.side w))
          (thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ (show TorusField n from d)))
      have h' : (show TorusField n from d') = _root_.YangMills.Construction.TorusFields.translate (siteOfInt (scaled ℓ.side w)) (show TorusField n from d) := h
      rw [h', torusHotSites_translate hfit hB.1, thickening_translateSet]
    simp only [localHullData]
    rw [hh]
    refine Prod.ext ?_ rfl
    ext z
    simp only [Finset.mem_inter, mem_translateSet']
  | succ s ih =>
    intro n _ hB w d d' Q h
    obtain ⟨h0, hV, hbad⟩ := h
    have hI := ih (n * ℓ.side) (isBlockTorusSide_mul hB hL0) (scaled ℓ.side w) d.1 d'.1 (sitesInBlocks ℓ.side Q) h0
    rw [localHullData_succ, localHullData_succ, sitesInBlocks_translateSet, hI, hV, hbad,
      hotCoreSites_translate hfit (T.stage s).toStepSetup rfl hB.1 w]
    have hf : ∀ B : Finset (TorusBond (n * ℓ.side)), (translateBonds (siteOfInt (scaled ℓ.side (scaled ℓ.side w))) B).filter
          (fun b => b.1 ∈ translateSet (siteOfInt (scaled ℓ.side (scaled ℓ.side w))) (sitesInBlocks ℓ.side Q)) =
        translateBonds (siteOfInt (scaled ℓ.side (scaled ℓ.side w))) (B.filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q) := by
      intro B
      ext c
      simp only [Finset.mem_filter, mem_translateBonds, mem_translateSet']
    have hc : translateSet (siteOfInt (scaled ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup d.2.2.1) ∩
          translateSet (siteOfInt (scaled ℓ.side w)) Q =
        translateSet (siteOfInt (scaled ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup d.2.2.1 ∩ Q) := by
      ext z
      simp only [Finset.mem_inter, mem_translateSet']
    rw [hf, hc]
    exact hullStep_translate T s₁ s n (scaled ℓ.side w) _ _ _ _
end Translates
section Assembly
variable {ℓ : StepParameters}
private theorem box_eq_translateSet {n : ℕ} [NeZero n] (z a : TorusSite n) (m : ℕ) :
    HullTrees.box z m = translateSet a (HullTrees.box (z + a) m) := by
  ext y
  rw [mem_translateSet']
  simp only [HullTrees.box, mem_thickening', Finset.mem_singleton, exists_eq_left, supDist_add_add]
private theorem hasExpansion_expansionCoupling (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hy : ℓ.y₁ ≤ x) (hrow : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by
  obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hret t x D hy hrow
  have hex : ∃ x' : ℝ, HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) := ⟨x', h1⟩
  have e : expansionCoupling ℓ t x D = hex.choose := by
    unfold expansionCoupling
    rw [dif_pos hex]
  obtain ⟨_, f, hf, _⟩ := hex.choose_spec
  have e2 := h3 _ f hf
  rw [e, e2]
  exact ⟨h1, h2⟩
private theorem hasExpansion_couplingFlow (hret : ExpansionReturnsAt ℓ) (β : ℝ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ t, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) → HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro h
    exact (hasExpansion_expansionCoupling hret (h t (by omega)) (ih fun j hj => h j (by omega))).1
private theorem stage_anchorRadius (T : StageTower ℓ) : ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => exact ih
private theorem localScore_depends_and_translate (hframe : FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T) (hfit : ℓ.Admissible) (s₁ : ℝ) (u n : ℕ)
    [NeZero n] (hB : IsBlockTorusSide ℓ n) (hbig : ∀ j ≤ u, 2 ^ 16 + ℓ.side ≤ stageRange T j)
    (hnear : ∀ j < u, stageRange T j ≤ stageRange T (j + 1) + 1)
    (hfr : ∀ s < u, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (V : TorusField n) (v : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaled ℓ.side v), c.2) =
        frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c)
    (z : TorusSite n) (D : ℝ) (k : ℕ) :
    DependsAbove ℓ u n (HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u)) (localScore rule T s₁ u n z D k) ∧
      ∀ (h : Fin 4 → ℤ) (p : TorusField (fineSide ℓ.side u n) × ChainNoise ℓ u n),
        localScore rule T s₁ u n z D k (pairTranslate ℓ u n (fun i => (ℓ.side : ℤ) * h i) p) =
          localScore rule T s₁ u n (z + siteOfInt fun i => (ℓ.side : ℤ) * h i) D k p := by
  classical
  refine ⟨?_, ?_⟩
  · intro W W' U U' hW hU
    by_cases hall : ∀ x, x ∈ HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u)
    · have e1 : W = W' := by
        funext x i
        have hb := mem_sitesUnder_of_forall ℓ.side u n _ hall
        exact hW (x, i) (hb _) (hb _)
      rw [e1, eq_of_noiseAgreeAbove_univ u n _ U U' hall hU]
    · replace hall := not_forall.1 hall
      have hQ : ∀ v ∈ localHullBox T u z D,
          IsDeepIn (5 * stageRange T u) (HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u)) v := by
        intro v hv
        obtain ⟨y, hy, hd⟩ := mem_thickening'.1 hv
        rw [Finset.mem_singleton.1 hy] at hd
        have hin : v ∈ HullTrees.box z (⌊2 * D⌋₊ + 6 * stageRange T u) :=
          mem_thickening'.2 ⟨z, Finset.mem_singleton_self _, by omega⟩
        refine ⟨hin, fun w hw => ?_⟩
        by_contra hlt
        refine hw (mem_thickening'.2 ⟨z, Finset.mem_singleton_self _, ?_⟩)
        have := _root_.YangMills.Construction.TorusFields.supDist_triangle w v z
        have e : _root_.YangMills.Construction.TorusFields.supDist w v = _root_.YangMills.Construction.TorusFields.supDist v w := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
        omega
      have key := localHullData_eq_of_agree hframe hblocks rule T hr hfit s₁ u hbig hnear u le_rfl n _
        (localHullBox T u z D) W W' U U' hW hU hQ hall
      show localScoreMoment T s₁ u n z D k _ = localScoreMoment T s₁ u n z D k _
      unfold localScoreMoment
      rw [key]
  · intro h p
    have hm := chain_isTranslateOf rule T hr hfit u hfr u le_rfl n hB h p
    have hh := localHullData_translate T hfit s₁ u n hB h _ _ (localHullBox T u (z + siteOfInt (scaled ℓ.side h)) D) hm
    have hbox : localHullBox T u z D =
        translateSet (siteOfInt (scaled ℓ.side h)) (localHullBox T u (z + siteOfInt (scaled ℓ.side h)) D) :=
      box_eq_translateSet z _ _
    show localScoreMoment T s₁ u n z D k _ = localScoreMoment T s₁ u n (z + siteOfInt (scaled ℓ.side h)) D k _
    unfold localScoreMoment
    rw [hbox, hh]
    simp only [mem_translateSet']
end Assembly
theorem localHullLocality (hframe : FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (hmoves : FrameCovariance) : localHullLocalityStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hdrawn _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨max Tb.floorMin (max (((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100) (Tb.B ^ 100)), ?_⟩
  intro y hy hret hwil g β K m T u n _ hat rule hrule z D k _ _
  have hfit := hdrawn.fits y ((le_max_left _ _).trans hy)
  have hy2 : ((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : Tb.B ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hB1 : 1 ≤ Tb.B := hdrawn.B_ge
  have hrun := hat.chain
  have hyB : Tb.B ≤ y := by
    have h1 : Tb.B ^ 1 ≤ Tb.B ^ 100 := pow_le_pow_right₀ hB1 (by norm_num)
    simpa using h1.trans hy3
  have hstand := hrun.follows
  have hfl : y ≤ (g ^ 2)⁻¹ := hrun.le_inv_sq
  have habove : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := hrun.upper_le
  have hpass := hrun.isFirst
  have hΞ : ∀ k < K, (g ^ 2)⁻¹ + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β k).1 := hpass.2
  have hβy : y ≤ β := by linarith
  have hrows := hasExpansion_couplingFlow hret β (hwil β hβy)
  have hlow : ∀ k < K, y ≤ (couplingFlow (Tb.stepParameters y) β k).1 := fun k hk => by
    have := hΞ k hk
    linarith
  have hmove : ∀ t < K, |(couplingFlow (Tb.stepParameters y) β (t + 1)).1 - (couplingFlow (Tb.stepParameters y) β t).1| ≤
      2 * Tb.B := fun t ht =>
    (hasExpansion_expansionCoupling hret (hlow t ht) (hrows t fun j hj => hlow j (by omega))).2
  have hxy : ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | rfl
    · exact hlow j h
    · cases j with
      | zero =>
        show y ≤ β
        exact hβy
      | succ t =>
        have h1 := abs_le.1 (hmove t (by omega))
        have h2 := hΞ t (by omega)
        linarith [h1.1]
  have hbig : ∀ j ≤ u, 2 ^ 16 + (Tb.stepParameters y).side ≤ stageRange T j := fun j hj => by
    have e : stageRange T j = clusterRange (couplingFlow (Tb.stepParameters y) β j).1 := by
      unfold stageRange
      rw [hstand j (by have := hat.le; omega)]
    rw [e]
    exact le_clusterRange (hy2.trans (hxy j (hj.trans hat.le)))
  have hnear : ∀ j < u, stageRange T j ≤ stageRange T (j + 1) + 1 := fun j hj => by
    have hK := hat.le
    have e : stageRange T j = clusterRange (couplingFlow (Tb.stepParameters y) β j).1 := by
      unfold stageRange
      rw [hstand j (by omega)]
    have e' : stageRange T (j + 1) = clusterRange (couplingFlow (Tb.stepParameters y) β (j + 1)).1 := by
      unfold stageRange
      rw [hstand (j + 1) (by omega)]
    rw [e, e']
    have h1 := abs_le.1 (hmove j (by omega))
    have h2 := hxy j (by omega)
    exact clusterRange_le_succ hB1 (hy3.trans (hxy (j + 1) (by omega))) (by linarith) (by linarith [h1.1])
  have hfr : ∀ s < u, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (V : TorusField n) (v : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord (Tb.stepParameters y) (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (_root_.YangMills.Construction.TorusFields.translate (siteOfInt v) V)
          (c.1 - siteOfInt (scaled (Tb.stepParameters y).side v), c.2) =
        frameCoord (Tb.stepParameters y) (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c := by
    intro s hs n _ hB V v c hc
    classical
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
    have hρ : (T.stage s).toStepSetup.anchorRadius = Tb.ρA := (stage_anchorRadius T s).trans hrun.anchor_bottom
    have hCC : ColdChainConstants (Tb.stepParameters y).coupling Tb.δ₁ (Tb.stepParameters y).side Tb.lam
        (T.stage s).toStepSetup.anchorRadius Tb.σA Tb.cg Tb.N := by
      rw [hρ]
      exact hdrawn.chain
    have hbs := hbig s (by omega)
    have hbs' := hbig (s + 1) hs
    have hRF : RangesAdmissible (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange :=
      ⟨hnear s hs, by
        show 2 ^ 16 ≤ stageRange T (s + 1)
        omega, (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        show 16 * 2 ^ 11 ≤ stageRange T s
        omega)⟩
    exact (hmoves (Tb.stepParameters y) Tb.δ₁ Tb.lam (T.stage s).toStepSetup.anchorRadius Tb.σA Tb.cg Tb.N hfit hCC
      hdrawn.σ_le (T.stage s).toStepSetup.depth (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange
      n V _ _ _ hRF (Or.inl ⟨hB, rfl, rfl, rfl⟩) c hc1 hc2).2 v
  have hBn : IsBlockTorusSide (Tb.stepParameters y) n := by
    have hL2 := hdrawn.L_ge
    have hn0 := hdrawn.n₀_ge
    have hvol : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hrun.volume_le
    have hLpos : 0 < Tb.side := by omega
    have hside : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
      rw [hat.side_eq]
      exact fineSide_eq _ _ _
    have hm : m ≠ 0 := by
      rintro rfl
      have : 1 * 4096 ≤ Tb.side * Tb.n₀ := Nat.mul_le_mul (by omega) hn0
      simp at hvol
      omega
    refine ⟨?_, ?_⟩
    · show Tb.side ∣ n
      rw [hside]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
    · show Tb.side * Tb.n₀ ≤ n
      rw [hside]
      exact hvol.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))
  exact localScore_depends_and_translate hframe hblocks rule T hrule hfit Kr.s₁ u n hBn hbig hnear hfr z D k
end YangMills.Construction.HullsInEveryVolume
end
