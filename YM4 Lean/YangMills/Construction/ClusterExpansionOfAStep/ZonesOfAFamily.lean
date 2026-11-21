import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettingsProof
import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinates
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours BlockSites BlockZones BlockTrees SpinFamilies TopLevelSites TorusFields TorusLumps
  StepSettings StepGas StepCosts BlockPlaces ClusterExpansionOfAStep
namespace FamilyZones
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ : Finset G.GasSpin}
section Geometry
variable {Z : Finset (TorusSite n)}
theorem exists_site_near_of_mem_core {θ : GasSupport R n} {u : TorusSite (n * R.params.side)}
    (h : parentBlock R.params.side u ∈ θ.core) :
    ∃ z ∈ θ.sites, supDist u z ≤ 4 * R.range + R.params.side := by apply _root_.YangMills.Construction.InBoxTransfer.exists_site_near_of_mem_core <;> assumption
theorem exists_anchor_near_of_mem_zone (hZ : IsRetainedZone G Z) {u : TorusSite (n * R.params.side)}
    (hu : parentBlock R.params.side u ∈ Z) :
    ∃ v ∈ G.anchorSites, supDist u v ≤ 4 * R.range + R.params.side := by apply _root_.YangMills.Construction.GasSettings.exists_anchor_near_of_mem_zone <;> assumption
theorem not_mem_zone_of_mem_core (hZ : IsRetainedZone G Z) (hfar : 64 * R.params.side ≤ R.range) (i : G.GasSpin)
    {y : TorusSite n} (hy : y ∈ i.1.core) : y ∉ Z := by
  classical
  intro hz
  obtain ⟨u, hu⟩ : ∃ u : TorusSite (n * R.params.side), parentBlock R.params.side u = y :=
    ⟨StepSettings.blockSite y (fun _ => 0), parentBlock_blockSite _ _⟩
  subst hu
  obtain ⟨a, ha, hau⟩ := exists_site_near_of_mem_core hy
  obtain ⟨v, hv, hvu⟩ := exists_anchor_near_of_mem_zone hZ hz
  have h1 := i.2.far_from_anchor a ha v hv
  have h2 := supDist_triangle a u v
  rw [supDist_comm a u] at h2
  omega
theorem mem_freeBlocks_iff {y : TorusSite n} (hZ : IsRetainedZone G Z) :
    y ∈ G.freeBlocks Γ ↔ y ∉ Z ∧ ∀ i : Γ, y ∉ i.1.1.core := by
  classical
  unfold GasGround.freeBlocks
  rw [hZ.zone_eq]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_biUnion, not_or, not_exists,
    not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, fun i => h3 i.1 i.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, fun i hi => h3 ⟨i, hi⟩⟩
theorem parentBlock_add_unitStep_of_isAxialTreeBond {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)) :
    parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) = parentBlock R.params.side x := by
  have h1 : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x +
      BlockAverages.unitStep (F := stepBlockFrame R.params.side n) 0 i) =
      enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x) := not_not.mp ht.1
  rw [← torusSiteInFrame_unitStep, ← BlockTrees.torusSiteInFrame_add] at h1
  exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
    ((_root_.YangMills.Construction.BlockTrees.enclosingCell_torusSiteInFrame _).symm.trans (h1.trans (_root_.YangMills.Construction.BlockTrees.enclosingCell_torusSiteInFrame x)))
theorem isRecorded_of_mem_cut (hZ : IsRetainedZone G Z) (hbig : 1 ≤ R.range) {x : TorusSite (n * R.params.side)}
    {i : Fin 4} (hx : parentBlock R.params.side x ∈ G.cut) : G.IsRecorded (x, i) := by
  classical
  have hat : x ∈ G.anchorSites := by
    unfold GasGround.anchorSites
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
  have hd : supDist (x + TorusFields.unitStep (n * R.params.side) i) x ≤ 4 * R.range := by
    have := supDist_add_unitStep_le x i
    rw [TorusFields.supDist_comm]
    omega
  rw [hZ.bond_iff, hZ.zone_eq]
  exact ⟨Finset.mem_union_left _ hx, Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near hat hd)⟩
theorem not_isRecorded_of_mem_coreBonds (hZ : IsRetainedZone G Z) (hfar : 64 * R.params.side ≤ R.range)
    {β : TorusBond (n * R.params.side)} {i : G.GasSpin} (hb : β ∈ i.1.coreBonds) : ¬ G.IsRecorded β := by
  classical
  intro hs
  exact not_mem_zone_of_mem_core hZ hfar i (Finset.mem_filter.mp hb).2.1 ((hZ.bond_iff β).mp hs).1
theorem mem_free_familySetting_iff (c : FamilyState G Γ) (hsep : (G.familyData c).CoresDisjoint)
    {β : TorusBond (n * R.params.side)} :
    β ∈ (G.familySetting c).free ↔
      β ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded β ∧ ∀ i : Γ, β ∉ i.1.1.coreBonds := by
  classical
  show β ∈ G.freeBonds.filter (fun b => (G.familyData c).fieldAt b = Sum.inl ()) ↔ _
  unfold GasGround.freeBonds
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun i hi => ?_⟩
    rw [fieldAt_familyData hsep i hi] at h3
    cases h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fieldAt_familyData_of_forall_not_mem c h3⟩
theorem free_familySetting_subset_chartBonds (c : FamilyState G Γ) :
    (G.familySetting c).free ⊆ chartBonds R.params.side n := by
  classical
  intro b hb
  have h := (mem_free_settingOf hb).1
  unfold markedBonds at h
  exact (Finset.mem_filter.mp h).1
theorem fine_familySetting_of_not_mem_free (c : FamilyState G Γ) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (h : (x, i) ∉ (G.familySetting c).free) :
    (G.familySetting c).fine x i = (G.settingWithFamily (G.familyData c)).fine x i := by
  classical
  show (G.settingWithFamily (G.familyData c)).field 0 x i = _
  unfold ChartSetting.field
  exact dif_neg h
theorem fine_familySetting_eq_ground (c : FamilyState G Γ) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (hf : (x, i) ∉ (G.familySetting c).free) (h : ∀ j : Γ, (x, i) ∉ j.1.1.coreBonds) :
    (G.familySetting c).fine x i = G.state.fieldWithStoredLinks (trivialField _) x i := by
  rw [fine_familySetting_of_not_mem_free c hf]
  simp only [GasGround.settingWithFamily]
  rw [fieldAt_familyData_of_forall_not_mem c h]
theorem fine_familySetting_eq_spin (c : FamilyState G Γ) (hsep : (G.familyData c).CoresDisjoint)
    {x : TorusSite (n * R.params.side)} {i : Fin 4} (hf : (x, i) ∉ (G.familySetting c).free) (j : Γ)
    (h : (x, i) ∈ j.1.1.coreBonds) : (G.familySetting c).fine x i = (c j).1 ⟨(x, i), h⟩ := by
  rw [fine_familySetting_of_not_mem_free c hf]
  simp only [GasGround.settingWithFamily]
  rw [fieldAt_familyData hsep j h]
theorem isChartCover_familySetting (hZ : IsRetainedZone G Z) (hbig : 1 ≤ R.range) (c : FamilyState G Γ)
    (hsep : (G.familyData c).CoresDisjoint) :
    (G.familySetting c).IsChartCover (G.freeBlocks Γ) := by
  classical
  refine ⟨free_familySetting_subset_chartBonds c, fun b hb ho => ?_, fun b hb => ?_⟩
  · have hC : parentBlock R.params.side b.1 ∉ G.cut := by
      intro hC
      have hs := isRecorded_of_mem_cut (i := b.2) hZ hbig hC
      obtain ⟨h1, h2⟩ := (hZ.bond_iff (b.1, b.2)).mp hs
      rcases ho with h | h
      · exact ((mem_freeBlocks_iff hZ).mp h).1 h1
      · exact ((mem_freeBlocks_iff hZ).mp h).1 h2
    refine (mem_free_familySetting_iff c hsep).mpr ⟨Finset.mem_filter.mpr ⟨hb, hC⟩, fun hs => ?_, fun i hi => ?_⟩
    · obtain ⟨h1, h2⟩ := (hZ.bond_iff b).mp hs
      rcases ho with h | h
      · exact ((mem_freeBlocks_iff hZ).mp h).1 h1
      · exact ((mem_freeBlocks_iff hZ).mp h).1 h2
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hi
      rcases ho with h | h
      · exact ((mem_freeBlocks_iff hZ).mp h).2 i h1
      · exact ((mem_freeBlocks_iff hZ).mp h).2 i h2
  · obtain ⟨-, hA, ht⟩ := Finset.mem_filter.mp hb
    have ho := (mem_freeBlocks_iff hZ).mp hA
    have hnf : (b.1, b.2) ∉ (G.familySetting c).free :=
      not_mem_free_of_isAxialTreeBond (free_familySetting_subset_chartBonds c) ht
    have hst : ∀ j : Γ, (b.1, b.2) ∉ j.1.1.coreBonds := fun j hj => ho.2 j (Finset.mem_filter.mp hj).2.1
    rw [fine_familySetting_eq_ground c hnf hst]
    have hnone : G.state.markAt (parentBlock R.params.side b.1) = none := by
      by_contra hc
      apply ho.1
      apply (hZ.recorded_iff _).mp
      exact Option.isSome_iff_ne_none.mpr hc
    unfold CoarseState.fieldWithStoredLinks
    rw [hnone]
    rfl
theorem fieldWithStoredLinks_overwriteField (hZ : IsRetainedZone G Z) (hbig : 1 ≤ R.range)
    (hfar : 64 * R.params.side ≤ R.range) (c : FamilyState G Γ) (hsep : (G.familyData c).CoresDisjoint)
    (W : TorusField (n * R.params.side)) :
    G.state.fieldWithStoredLinks (G.overwriteField c W) = (G.familySetting c).glueOver (G.freeBlocks Γ) W := by
  classical
  funext x i
  unfold ChartSetting.glueOver
  by_cases hs : G.IsRecorded (x, i)
  · have hnf : (x, i) ∉ (G.familySetting c).free := fun h => ((mem_free_familySetting_iff c hsep).mp h).2.1 hs
    have hj : ∀ j : Γ, (x, i) ∉ j.1.1.coreBonds := fun j h => not_isRecorded_of_mem_coreBonds hZ hfar h hs
    have hnt : (x, i) ∉ axialTreeBonds R.params.side (G.freeBlocks Γ) := fun h =>
      ((mem_freeBlocks_iff hZ).mp (Finset.mem_filter.mp h).2.1).1 ((hZ.bond_iff _).mp hs).1
    rw [if_neg (fun h => h.elim hnf hnt), fine_familySetting_eq_ground c hnf hj]
    obtain ⟨st, h1, h2⟩ := hs
    unfold CoarseState.fieldWithStoredLinks
    rw [h1]
    rcases hv : st.linkValue (siteOffset (x, i).1, (x, i).2) with u | g
    · simp [hv] at h2
    · simp only [hv]
  · have hfo : ∀ W' : TorusField (n * R.params.side), G.state.fieldWithStoredLinks W' x i = W' x i := by
      intro W'
      unfold CoarseState.fieldWithStoredLinks
      rcases h1 : G.state.markAt (parentBlock R.params.side x) with _ | st
      · rfl
      · rcases hv : st.linkValue (siteOffset x, i) with u | g
        · simp only [hv]
        · exact absurd ⟨st, h1, by simp [hv]⟩ hs
    rw [hfo]
    by_cases hj : ∃ j : Γ, (x, i) ∈ j.1.1.coreBonds
    · obtain ⟨j, hj⟩ := hj
      have hnf : (x, i) ∉ (G.familySetting c).free := fun h => ((mem_free_familySetting_iff c hsep).mp h).2.2 j hj
      have hnt : (x, i) ∉ axialTreeBonds R.params.side (G.freeBlocks Γ) := fun h =>
        ((mem_freeBlocks_iff hZ).mp (Finset.mem_filter.mp h).2.1).2 j (Finset.mem_filter.mp hj).2.1
      rw [if_neg (fun h => h.elim hnf hnt), fine_familySetting_eq_spin c hsep hnf j hj]
      unfold GasGround.overwriteField
      rw [fieldAt_familyData hsep j hj]
    · have hj' : ∀ j : Γ, (x, i) ∉ j.1.1.coreBonds := fun j h => hj ⟨j, h⟩
      have ho : G.overwriteField c W x i = W x i := by
        unfold GasGround.overwriteField
        rw [fieldAt_familyData_of_forall_not_mem c hj']
      rw [ho, if_pos]
      by_cases ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
      · right
        have hsame := parentBlock_add_unitStep_of_isAxialTreeBond ht
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_freeBlocks_iff hZ).mpr ⟨fun h => hs ?_, fun j h => hj' j ?_⟩, ht⟩
        · exact (hZ.bond_iff _).mpr ⟨h, by simpa only [hsame] using h⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, by simpa only [hsame] using h⟩
      · left
        refine (mem_free_familySetting_iff c hsep).mpr
          ⟨Finset.mem_filter.mpr ⟨?_, fun hC => hs (isRecorded_of_mem_cut hZ hbig hC)⟩, hs, hj'⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
end Geometry
theorem exists_hot_data (hh : G.IsHotCase) : ∃ (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
  coarseStateOf R G.cut W Yt ωt bad b = G.state ∧ bad ⊆ markedBonds R G.cut ∧
  (open Classical in bad.image Prod.fst ∪ Yt ⊆ attachedSites R.params.side R.range bad Yt G.cut) ∧
  G.recordedBad = bad ∧ G.recordedSites = Yt ∧
  IsRetainedZone G (storedBlocks R.params.side R.range bad Yt G.cut) ∧
  ∀ y, G.state.markAt y = if y ∈ storedBlocks R.params.side R.range bad Yt G.cut then
    some (blockConfigAt R G.cut (storedBlocks R.params.side R.range bad Yt G.cut) W Yt ωt bad b y) else none := by
  classical
  obtain ⟨W, Yt, ωt, bad, b, hq, _, hmk, hall, _, _, _⟩ := hh.exists_state
  set Z := storedBlocks R.params.side R.range bad Yt G.cut with hZ
  have hstore : ∀ y, G.state.markAt y =
      if y ∈ Z then some (blockConfigAt R G.cut Z W Yt ωt bad b y) else none := by
    intro y
    rw [← hq, _root_.YangMills.Construction.BlockZones.markAt_coarseStateOf]
  have hatt := attachedSites_eq_of_subset hall
  have hcore : ∀ z ∈ bad.image Prod.fst ∪ Yt, parentBlock R.params.side z ∈ Z := fun z hz => by
    rw [hZ]
    unfold storedBlocks
    exact Finset.mem_union_right _ (parentBlock_mem_coreBlocks (hall hz))
  have hbad : G.recordedBad = bad := by
    ext c
    unfold GasGround.recordedBad
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hstore]
    constructor
    · rintro ⟨s, hs, hb⟩
      by_cases hy : parentBlock R.params.side c.1 ∈ Z
      · rw [if_pos hy] at hs
        have := Option.some.inj hs
        subst this
        unfold blockConfigAt at hb
        simp only [decide_eq_true_eq, BlockPlaces.blockSite_parentBlock_siteOffset] at hb
        exact hb
      · rw [if_neg hy] at hs
        exact absurd hs (by simp)
    · intro hc
      have hy : parentBlock R.params.side c.1 ∈ Z :=
        hcore _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
      refine ⟨_, if_pos hy, ?_⟩
      unfold blockConfigAt
      simp only [decide_eq_true_eq, BlockPlaces.blockSite_parentBlock_siteOffset]
      exact hc
  have hsites : G.recordedSites = Yt := by
    ext z
    unfold GasGround.recordedSites CoarseState.labelAt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hstore]
    constructor
    · intro h
      by_cases hy : parentBlock R.params.side z ∈ Z
      · rw [if_pos hy] at h
        simp only [blockConfigAt, BlockPlaces.blockSite_parentBlock_siteOffset] at h
        by_contra hz
        simp [hz] at h
      · rw [if_neg hy] at h
        simp at h
    · intro hz
      have hy : parentBlock R.params.side z ∈ Z := hcore _ (Finset.mem_union_right _ hz)
      rw [if_pos hy]
      simp only [blockConfigAt, BlockPlaces.blockSite_parentBlock_siteOffset]
      simp [hz]
  have hattG : G.anchorSites = attachedSites R.params.side R.range bad Yt G.cut := by
    rw [hatt]
    unfold GasGround.anchorSites
    rw [hbad, hsites]
  refine ⟨W, Yt, ωt, bad, b, hq, hmk, hall, hbad, hsites, ?_, hstore⟩
  obtain ⟨Z', hZ'⟩ := exists_isAdmissibleZone G (Or.inr hh)
  have e : Z' = Z := by
    rw [hZ'.zone_eq, hattG]
    rfl
  rw [← hZ, ← e]
  exact hZ'
theorem fillLabels_of_unlabelled {Yt : Finset (TorusSite (n * R.params.side))}
    (ν : G.state.unlabelled Yt → R.labels.Ω) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ Yt) (h : G.state.labelAt z = Sum.inl ()) (hr : z ∈ G.state.unlabelled Yt) :
    G.state.fillLabels Yt ν ⟨z, hz⟩ = ν ⟨z, hr⟩ := by
  unfold CoarseState.fillLabels
  split
  · rename_i a heq
    rw [h] at heq
    cases heq
  · rfl
theorem fillLabels_of_labelled {Yt : Finset (TorusSite (n * R.params.side))}
    (ν : G.state.unlabelled Yt → R.labels.Ω) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ Yt) {a : R.labels.Ω} (h : G.state.labelAt z = Sum.inr a) :
    G.state.fillLabels Yt ν ⟨z, hz⟩ = a := by
  unfold CoarseState.fillLabels
  split
  · rename_i a' heq
    rw [h] at heq
    exact (Sum.inr.inj heq).symm
  · rename_i u heq
    rw [h] at heq
    cases heq
theorem not_mem_recordedSites_of_mem_sites (i : G.GasSpin) {z : TorusSite (n * R.params.side)} (hz : z ∈ i.1.2) :
    z ∉ G.recordedSites := by
  classical
  intro hs
  have h1 := i.2.far_from_anchor z (Finset.mem_union_right _ hz) z (by
    unfold GasGround.anchorSites
    exact Finset.mem_union_right _ hs)
  rw [supDist_self] at h1
  omega
theorem labelAt_eq_inl_of_not_mem_recordedSites {z : TorusSite (n * R.params.side)} (hz : z ∉ G.recordedSites) :
    G.state.labelAt z = Sum.inl () := by
  classical
  by_contra h
  apply hz
  unfold GasGround.recordedSites
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases hl : G.state.labelAt z with u | a
  · exact absurd hl h
  · rfl
theorem siteOffset_blockSite {L : ℕ} [NeZero L] (y : TorusSite n) (o : BlockOffset L) :
    siteOffset (n := n) (L := L) (StepSettings.blockSite y o) = o := by
  funext i
  apply Fin.ext
  set m : ℤ := ((L : ℤ) - 1) / 2 with hm
  set z : ℤ := (L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - m) with hz
  have hx : StepSettings.blockSite (L := L) y o i = ((z : ℤ) : ZMod (n * L)) := rfl
  set c : ℤ := ((StepSettings.blockSite (L := L) y o i).cast : ℤ) with hc
  have hcz : ((c : ℤ) : ZMod (n * L)) = ((z : ℤ) : ZMod (n * L)) := by
    rw [← hx, hc]
    exact ZMod.intCast_zmod_cast _
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcz
  have hmod : (c + m) % (L : ℤ) = ((o i : ℕ) : ℤ) := by
    have e1 : c + m = ((o i : ℕ) : ℤ) + (L : ℤ) * (((y i).cast : ℤ) - n * e) := by
      push_cast at he
      have : z - c = (n : ℤ) * L * e := he
      have hz' : z = (L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - m) := hz
      linear_combination hz' - this
    rw [e1, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (o i).2)
  unfold siteOffset
  simp only [Fin.ofNat, Fin.val_mk]
  rw [← hc, hmod]
  simp only [Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (o i).2
theorem coarseState_ext {Y Y' : Finset (TorusSite n)} (e : Y = Y')
    {f : Y → CoarseLabel R.labels.Ω R.params.side} {f' : Y' → CoarseLabel R.labels.Ω R.params.side}
    (h : ∀ y (hy : y ∈ Y) (hy' : y ∈ Y'), f ⟨y, hy⟩ = f' ⟨y, hy'⟩) :
    (⟨Y, f⟩ : CoarseState R n) = ⟨Y', f'⟩ := by
  subst e
  congr 1
  funext y
  exact h y.1 y.2 y.2
open Classical in
theorem coarseStateOf_congr {C : Finset (TorusSite n)} {W W' : TorusField (n * R.params.side)}
    {Y Y' : Finset (TorusSite (n * R.params.side))} {ω : Y → R.labels.Ω} {ω' : Y' → R.labels.Ω}
    {bad bad' : Finset (TorusBond (n * R.params.side))} {b b' : BaseChoice R.params.side n}
    (hZ : storedBlocks R.params.side R.range bad Y C = storedBlocks R.params.side R.range bad' Y' C)
    (hs : ∀ y ∈ storedBlocks R.params.side R.range bad Y C,
      blockConfigAt R C (storedBlocks R.params.side R.range bad Y C) W Y ω bad b y =
      blockConfigAt R C (storedBlocks R.params.side R.range bad Y C) W' Y' ω' bad' b' y) :
    coarseStateOf R C W Y ω bad b = coarseStateOf R C W' Y' ω' bad' b' := by
  unfold coarseStateOf
  refine coarseState_ext (by unfold coarseHull; rw [hZ]) fun y hy hy' => ?_
  by_cases h : y ∈ storedBlocks R.params.side R.range bad Y C
  · rw [if_pos h, if_pos (hZ ▸ h), hs y h, hZ]
  · rw [if_neg h, if_neg (hZ ▸ h)]
theorem blockConfig_ext {Ω : Type} {L : ℕ} {s s' : BlockLabels Ω L} (h1 : s.isCore = s'.isCore)
    (h2 : s.badBond = s'.badBond) (h3 : s.siteLabel = s'.siteLabel) (h4 : s.basePoint = s'.basePoint)
    (h5 : s.linkValue = s'.linkValue) : s = s' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.blockConfig_ext <;> assumption
theorem parentBlock_toTorusSite_of_enclosingCell {e : (stepBlockFrame R.params.side n).Cell}
    {x : (stepBlockFrame R.params.side n).Site 0} (h : enclosingCell x = e) :
    parentBlock R.params.side (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) x) =
      cellBlock R.params.side n e := by
  have h1 := _root_.YangMills.Construction.BlockTrees.enclosingCell_torusSiteInFrame (n := n) (L := R.params.side)
    (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) x)
  rw [torusSiteInFrame_toTorusSite (fun k => stepBlockFrame_period_zero k), h] at h1
  have h2 := congrArg (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n) h1
  rw [toTorusSite_torusSiteInFrame (fun k => stepBlockFrame_period_one k)] at h2
  exact h2.symm
theorem eq_frameBlockSite_siteOffset {e : (stepBlockFrame R.params.side n).Cell}
    {x : (stepBlockFrame R.params.side n).Site 0} (h : enclosingCell x = e) :
    x = frameBlockSite R.params.side n (cellBlock R.params.side n e)
      (siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) x)) := by
  unfold frameBlockSite
  rw [← parentBlock_toTorusSite_of_enclosingCell h, BlockPlaces.blockSite_parentBlock_siteOffset,
    torusSiteInFrame_toTorusSite (fun k => stepBlockFrame_period_zero k)]
theorem enclosingCell_cellCentre (hfit : R.params.Admissible) (e : (stepBlockFrame R.params.side n).Cell) :
    enclosingCell (cellCentre (F := stepBlockFrame R.params.side n) 0 e : (stepBlockFrame R.params.side n).Site 0) =
      e := by
  have hL : Odd (stepBlockFrame R.params.side n).blockSide := hfit.L_odd
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube ((stepBlockFrame R.params.side n).blockSide ^
      ((stepBlockFrame R.params.side n).top - 0)) := by
    have hp : (1 : ℤ) ≤ (((stepBlockFrame R.params.side n).blockSide ^
        ((stepBlockFrame R.params.side n).top - 0) : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_pow _ _ hL.pos
    have hq : 0 ≤ ((((stepBlockFrame R.params.side n).blockSide ^
        ((stepBlockFrame R.params.side n).top - 0) : ℕ) : ℤ) - 1) / 2 := Int.ediv_nonneg (by linarith) (by norm_num)
    exact Fintype.mem_piFinset.2 fun _ => Finset.mem_Icc.2 ⟨by simpa using hq, by simpa using hq⟩
  have h1 := enclosingCell_cellCentre_add (F := stepBlockFrame R.params.side n) hL (j := 0) e 0 h0
  have e0 : (BlockAverages.siteOfCoords 0 (0 : Fin 4 → ℤ) : (stepBlockFrame R.params.side n).Site 0) = 0 := by
    funext i
    simp [BlockAverages.siteOfCoords]
  rw [e0, add_zero] at h1
  exact h1
theorem mem_of_mem_filter_inst {α : Type*} {p : α → Prop} {d : DecidablePred p} {s : Finset α} {x : α}
    (h : x ∈ @Finset.filter α p d s) : x ∈ s := (Finset.mem_filter.mp h).1
theorem enclosingCell_of_mem_baseSitesAt (hfit : R.params.Admissible) (hn : 0 < n)
    {H : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))}
    {e : (stepBlockFrame R.params.side n).Cell} {z : (stepBlockFrame R.params.side n).Site 0}
    (hz : z ∈ baseSitesAt R.params.baseDepth H e) : enclosingCell z = e := by
  classical
  have hL : Odd (stepBlockFrame R.params.side n).blockSide := hfit.L_odd
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => hn
  unfold baseSitesAt at hz
  split_ifs at hz with hc
  · rw [Finset.mem_singleton.mp hz]
    exact enclosingCell_cellCentre hfit e
  · exact enclosingCell_eq_of_mem_sitesBelow hL hs (mem_of_mem_filter_inst hz)
theorem enclosingCell_baseChoice (hfit : R.params.Admissible) (hn : 0 < n) {b : BaseChoice R.params.side n}
    {H : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))}
    (hb : IsBaseChoice R.params.baseDepth H b) (e : (stepBlockFrame R.params.side n).Cell) :
    enclosingCell (b e) = e := by
  classical
  have hL : Odd (stepBlockFrame R.params.side n).blockSide := hfit.L_odd
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => hn
  by_cases hc : nearbyLumps H e = ∅ ∨ IsCrowded R.params.baseDepth H e
  · rw [(hb e).1 hc]
    exact enclosingCell_cellCentre hfit e
  · exact enclosingCell_eq_of_mem_sitesBelow hL hs ((hb e).2 hc).1
theorem frameBlockSite_injective {L : ℕ} [NeZero L] (y : TorusSite n) {o o' : BlockOffset L}
    (h : frameBlockSite L n y o = frameBlockSite L n y o') : o = o' := by
  have hp : ∀ i, (stepBlockFrame L n).period 0 i = n * L := fun i => by
    simp [stepBlockFrame, BlockFrame.period, BlockFrame.top]
  have e : StepSettings.blockSite (L := L) y o = StepSettings.blockSite y o' := by
    have h1 := congrArg (toTorusSite (F := stepBlockFrame L n) (j := 0) (n * L)) h
    unfold frameBlockSite at h1
    rwa [toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp] at h1
  rw [← siteOffset_blockSite (n := n) y o, ← siteOffset_blockSite (n := n) y o', e]
theorem sigma_labelling_ext {Ω : Type} {m : ℕ} {Y Y' : Finset (TorusSite m)} (e : Y = Y') {ω : Y → Ω}
    {ω' : Y' → Ω} (h : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    (⟨Y, ω⟩ : Σ Y : Finset (TorusSite m), Y → Ω) = ⟨Y', ω'⟩ := by
  subst e
  congr 1
  funext z
  exact h z.1 z.2 z.2
theorem familySites_fillLabels_eq (c : FamilyState G Γ)
    (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω) (hsep : (G.familyData c).CoresDisjoint)
    (hν : ∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2)
      (hr : z ∈ G.state.unlabelled (G.familySites Γ)), ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩) :
    (⟨G.familySites Γ, G.state.fillLabels _ ν⟩ : Σ Y : Finset (TorusSite (n * R.params.side)), Y → R.labels.Ω) =
      ⟨(G.familySetting c).support, (G.familySetting c).labelling⟩ := by
  classical
  refine sigma_labelling_ext (support_familySetting c).symm fun z hz hz' => ?_
  show _ = (G.settingWithFamily (G.familyData c)).labelling ⟨z, hz'⟩
  simp only [GasGround.settingWithFamily]
  by_cases hs : z ∈ (G.familyData c).sites
  · rw [dif_pos hs]
    have hs' := hs
    rw [sites_familyData] at hs'
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hs'
    have hnot := not_mem_recordedSites_of_mem_sites i hzi
    have hl := labelAt_eq_inl_of_not_mem_recordedSites hnot
    have hr : z ∈ G.state.unlabelled (G.familySites Γ) := Finset.mem_filter.mpr ⟨hz, hl⟩
    rw [fillLabels_of_unlabelled ν hz hl hr, hν ⟨i, hi⟩ z hzi hr,
      GasFamily.labelAt_eq_of_mem _ hsep hs ((occupies_familyData_iff c).mpr ⟨⟨i, hi⟩, rfl⟩) hzi,
      state_familyData]
  · rw [dif_neg hs]
    have hst : z ∈ G.recordedSites := by
      rcases Finset.mem_union.mp hz' with a | a
      · exact a
      · exact absurd a hs
    have hr := (Finset.mem_filter.mp hst).2
    obtain ⟨a, ha⟩ : ∃ a, G.state.labelAt z = Sum.inr a := by
      rcases hl : G.state.labelAt z with u | a
      · rw [hl] at hr
        simp at hr
      · exact ⟨a, rfl⟩
    have key : ∀ (x : WithNone R.labels.Ω) (h : x.isRight = true), x = Sum.inr a → x.getRight h = a := by
      rintro _ _ rfl
      rfl
    rw [fillLabels_of_labelled ν hz ha]
    exact (key _ _ ha).symm
end FamilyZones
end YangMills.Construction
end
