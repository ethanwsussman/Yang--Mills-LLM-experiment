import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ClassBesideAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ClassesBesideAFarSet
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepGas StepSettings StepCosts BlockOffsets BlockPlaces
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem mem_coreBlocks_iff_exists {L r : ℕ} [NeZero L] {A : Finset (TorusSite (n * L))} {y : TorusSite n} :
    y ∈ coreBlocks L r A ↔ ∃ p : TorusSite (n * L), parentBlock L p = y ∧ ∃ z ∈ A, _root_.YangMills.Construction.TorusFields.supDist p z ≤ 4 * r := by
  classical
  unfold coreBlocks
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hp
    obtain ⟨z, hz, hpz⟩ := (mem_thickening _ _ _).mp h2
    exact ⟨p, by simpa [sitesInBlocks] using h1, z, hz, hpz⟩
  · rintro ⟨p, hp, z, hz, hpz⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨by simpa [sitesInBlocks] using hp, (mem_thickening _ _ _).mpr ⟨z, hz, hpz⟩⟩⟩
theorem mem_sitesInBlocks_iff {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
theorem mem_coreBlocks_of_sitesInBlocks_subset {L r : ℕ} [NeZero L] {S : Finset (TorusSite n)}
    {A : Finset (TorusSite (n * L))} (hA : sitesInBlocks L S ⊆ A) {y : TorusSite n} (hy : y ∈ S) :
    y ∈ coreBlocks L r A := by
  have hb : parentBlock L (blockSite y (fun _ => 0 : BlockOffset L) : TorusSite (n * L)) = y := parentBlock_blockSite y _
  refine mem_coreBlocks_iff_exists.mpr ⟨_, hb, _, hA (mem_sitesInBlocks_iff.mpr (hb.symm ▸ hy)), by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩
structure _root_.YangMills.Construction.StepGas.GasGround.RecordsCore (G : GasGround R n) : Prop where
  isRecorded_iff : ∀ b : TorusBond (n * R.params.side), G.IsRecorded b ↔
    parentBlock R.params.side b.1 ∈ coreBlocks R.params.side R.range G.anchorSites ∧
    parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ coreBlocks R.params.side R.range G.anchorSites
  markAt_eq_none : ∀ y, y ∉ coreBlocks R.params.side R.range G.anchorSites → G.state.markAt y = none
theorem _root_.YangMills.Construction.StepGas.GasGround.sitesInBlocks_cut_subset_anchorSites (G : GasGround R n) :
    sitesInBlocks R.params.side G.cut ⊆ G.anchorSites := by
  classical
  intro z hz
  unfold StepGas.GasGround.anchorSites
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
theorem _root_.YangMills.Construction.StepGas.GasGround.recordsCore_of_isColdCase (G : GasGround R n)
    (h : G.IsColdCase) : G.RecordsCore := by
  classical
  have hnone : ∀ y, G.state.markAt y = none := by
    intro y
    unfold CoarseState.markAt
    rw [dif_neg]
    rw [h.state_empty]
    exact Finset.notMem_empty y
  have hat : G.anchorSites = ∅ := by
    unfold StepGas.GasGround.anchorSites
    have h1 : sitesInBlocks R.params.side G.cut = ∅ := by
      rw [h.cut_eq]
      ext x
      simp [sitesInBlocks]
    have h2 : G.recordedBad = ∅ := by
      unfold StepGas.GasGround.recordedBad
      ext b
      simp [hnone]
    have h3 : G.recordedSites = ∅ := by
      unfold StepGas.GasGround.recordedSites
      ext z
      simp [CoarseState.labelAt, hnone]
    rw [h1, h2, h3]
    simp
  refine ⟨fun b => ?_, fun y _ => hnone y⟩
  rw [hat]
  constructor
  · rintro ⟨s, hs, -⟩
    rw [hnone] at hs
    exact absurd hs (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨_, _, z, hz, _⟩ := mem_coreBlocks_iff_exists.mp h1
    exact absurd hz (Finset.notMem_empty z)
theorem _root_.YangMills.Construction.StepGas.GasGround.recordsCore_of_isHotCase (G : GasGround R n)
    (h : G.IsHotCase) : G.RecordsCore := by
  classical
  obtain ⟨W, Yt, ωt, bad, b, hq, -, -, hsub, -, -, -⟩ := h.exists_state
  have hstore : ∀ y, G.state.markAt y = if y ∈ storedBlocks R.params.side R.range bad Yt G.cut then
      some (blockConfigAt R G.cut (storedBlocks R.params.side R.range bad Yt G.cut) W Yt ωt bad b y) else none := by
    intro y
    rw [← hq]
    unfold CoarseState.markAt coarseStateOf
    by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · have hyH : y ∈ coarseHull R.params.side R.range R.nextRange bad Yt G.cut :=
        (mem_thickening _ _ _).mpr ⟨y, hy, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩
      simp [hyH, hy]
    · by_cases hyH : y ∈ coarseHull R.params.side R.range R.nextRange bad Yt G.cut
      · simp [hyH, hy]
      · simp [hyH, hy]
  have hU : attachedSites R.params.side R.range bad Yt G.cut =
      sitesInBlocks R.params.side G.cut ∪ bad.image Prod.fst ∪ Yt := by
    ext z
    constructor
    · intro hz
      unfold attachedSites at hz
      obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
      have h1 := subset_of_mem_chainComponents (Finset.mem_filter.mp hX).1 hzX
      simp only [Finset.mem_union] at h1 ⊢
      tauto
    · intro hz
      simp only [Finset.mem_union] at hz
      rcases hz with (hz | hz) | hz
      · have hzU : z ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks R.params.side G.cut :=
          Finset.mem_union_right _ hz
        obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * R.range) hzU
        refine Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, z, Finset.mem_inter.mpr ⟨hzX, hz⟩⟩, hzX⟩
      · exact hsub (Finset.mem_union_left _ hz)
      · exact hsub (Finset.mem_union_right _ hz)
  have hZfirst : ∀ x ∈ bad.image Prod.fst ∪ Yt,
      parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt G.cut := by
    intro x hx
    refine Finset.mem_union_right _ (mem_coreBlocks_iff_exists.mpr ⟨x, rfl, x, hsub hx, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩)
  have hbad : G.recordedBad = bad := by
    ext c
    unfold StepGas.GasGround.recordedBad
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hstore]
    constructor
    · rintro ⟨s, hs, hb⟩
      by_cases hy : parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt G.cut
      · rw [if_pos hy] at hs
        obtain rfl := Option.some.inj hs
        have := of_decide_eq_true hb
        rwa [show ((blockSite (parentBlock R.params.side c.1) (siteOffset c.1) : TorusSite (n * R.params.side)), c.2) = c from by
          rw [blockSite_parentBlock_siteOffset]] at this
      · rw [if_neg hy] at hs
        exact absurd hs (by simp)
    · intro hc
      have hy := hZfirst c.1 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
      refine ⟨_, if_pos hy, ?_⟩
      simp only [blockConfigAt]
      rw [blockSite_parentBlock_siteOffset]
      simpa using hc
  have hsites : G.recordedSites = Yt := by
    ext z
    unfold StepGas.GasGround.recordedSites
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold CoarseState.labelAt
    rw [hstore]
    by_cases hy : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · rw [if_pos hy]
      simp only [blockConfigAt]
      rw [blockSite_parentBlock_siteOffset]
      by_cases hz : z ∈ Yt
      · simp [hz]
      · simp [hz]
    · rw [if_neg hy]
      constructor
      · intro h0
        simp at h0
      · intro hz
        exact absurd (hZfirst z (Finset.mem_union_right _ hz)) hy
  have hatt : G.anchorSites = attachedSites R.params.side R.range bad Yt G.cut := by
    unfold StepGas.GasGround.anchorSites
    rw [hbad, hsites, hU]
  have hZ : ∀ y, y ∈ storedBlocks R.params.side R.range bad Yt G.cut ↔
      y ∈ coreBlocks R.params.side R.range G.anchorSites := by
    intro y
    unfold storedBlocks
    rw [Finset.mem_union, hatt]
    constructor
    · rintro (hy | hy)
      · exact mem_coreBlocks_of_sitesInBlocks_subset (hatt ▸ G.sitesInBlocks_cut_subset_anchorSites) hy
      · exact hy
    · exact Or.inr
  refine ⟨fun c => ?_, fun y hy => ?_⟩
  · rw [← hZ, ← hZ]
    unfold StepGas.GasGround.IsRecorded
    rw [hstore]
    constructor
    · rintro ⟨s, hs, hr⟩
      by_cases hy : parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt G.cut
      · rw [if_pos hy] at hs
        obtain rfl := Option.some.inj hs
        refine ⟨hy, ?_⟩
        by_contra hn
        simp only [blockConfigAt, blockSite_parentBlock_siteOffset, if_neg hn] at hr
        simp at hr
      · rw [if_neg hy] at hs
        exact absurd hs (by simp)
    · rintro ⟨h1, h2⟩
      refine ⟨_, if_pos h1, ?_⟩
      simp only [blockConfigAt, blockSite_parentBlock_siteOffset, if_pos h2]
      rfl
  · rw [hstore, if_neg fun h0 => hy ((hZ y).mp h0)]
theorem _root_.YangMills.Construction.StepGas.GasGround.recordsCore (G : GasGround R n)
    (h : G.IsAdmissibleGround) : G.RecordsCore :=
  h.elim G.recordsCore_of_isColdCase G.recordsCore_of_isHotCase
section Membership
variable (G : GasGround R n) (γ : GasFamily R n)
theorem mem_coreBonds_iff {θ : GasSupport R n} {b : TorusBond (n * R.params.side)} :
    b ∈ θ.coreBonds ↔ parentBlock R.params.side b.1 ∈ θ.core ∧
      parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ θ.core := by
  classical
  unfold GasSupport.coreBonds
  simp
theorem fieldAt_eq_inl_iff {b : TorusBond (n * R.params.side)} :
    γ.fieldAt b = Sum.inl () ↔ ¬ ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds := by
  classical
  unfold GasFamily.fieldAt
  by_cases h : ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds
  · rw [dif_pos h]
    simp [h]
  · rw [dif_neg h]
    simp [h]
theorem mem_gatheredSites_iff {z : TorusSite (n * R.params.side)} :
    z ∈ (G.familyCore γ).badBonds.image Prod.fst ∪ (G.settingOf γ).support ∪
        sitesInBlocks R.params.side (G.familyCore γ).core ↔
      z ∈ G.anchorSites ∨ ∃ θ, γ.Occupies θ ∧ z ∈ θ.sites := by
  classical
  show z ∈ (G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst).image Prod.fst ∪
    (G.recordedSites ∪ γ.sites) ∪ sitesInBlocks R.params.side G.cut ↔ _
  unfold StepGas.GasGround.anchorSites GasFamily.sites
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ((⟨b, hb | ⟨θ, hθ, hb⟩, rfl⟩ | h | ⟨θ, hθ, h⟩) | h)
    · exact Or.inl (Or.inl (Or.inr ⟨b, hb, rfl⟩))
    · exact Or.inr ⟨θ, hθ, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨θ, hθ, Finset.mem_union_right _ h⟩
    · exact Or.inl (Or.inl (Or.inl h))
  · rintro (((h | ⟨b, hb, rfl⟩) | h) | ⟨θ, hθ, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨b, Or.inl hb, rfl⟩)
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl (Or.inl ⟨b, Or.inr ⟨θ, hθ, hb⟩, rfl⟩)
      · exact Or.inl (Or.inr (Or.inr ⟨θ, hθ, h⟩))
theorem mem_storedBlockSet_iff {y : TorusSite n} : y ∈ (G.settingOf γ).storedBlockSet (G.familyCore γ) ↔
    y ∈ coreBlocks R.params.side R.range G.anchorSites ∨ ∃ θ, γ.Occupies θ ∧ y ∈ θ.core := by
  classical
  unfold ChartSetting.storedBlockSet ChartSetting.storedComponents clusterComponents
  rw [biUnion_chainComponents, Finset.mem_union]
  constructor
  · rintro (hy | hy)
    · exact Or.inl (mem_coreBlocks_of_sitesInBlocks_subset G.sitesInBlocks_cut_subset_anchorSites hy)
    · obtain ⟨p, hp, z, hz, hpz⟩ := mem_coreBlocks_iff_exists.mp hy
      rcases (mem_gatheredSites_iff G γ).mp hz with hz | ⟨θ, hθ, hz⟩
      · exact Or.inl (mem_coreBlocks_iff_exists.mpr ⟨p, hp, z, hz, hpz⟩)
      · exact Or.inr ⟨θ, hθ, GasSupport.mem_core.mpr ⟨p, hp, z, hz, hpz⟩⟩
  · rintro (hy | ⟨θ, hθ, hy⟩)
    · obtain ⟨p, hp, z, hz, hpz⟩ := mem_coreBlocks_iff_exists.mp hy
      exact Or.inr (mem_coreBlocks_iff_exists.mpr ⟨p, hp, z, (mem_gatheredSites_iff G γ).mpr (Or.inl hz), hpz⟩)
    · obtain ⟨p, hp, z, hz, hpz⟩ := GasSupport.mem_core.mp hy
      exact Or.inr (mem_coreBlocks_iff_exists.mpr
        ⟨p, hp, z, (mem_gatheredSites_iff G γ).mpr (Or.inr ⟨θ, hθ, hz⟩), hpz⟩)
theorem false_of_adjacent_in_far_cores {L r : ℕ} [NeZero L] (hL : 2 * L + 1 ≤ 2 * r)
    {A B : Finset (TorusSite (n * L))}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, 10 * r < _root_.YangMills.Construction.TorusFields.supDist a b) {p q : TorusSite (n * L)}
    (hp : parentBlock L p ∈ coreBlocks L r A)
    (hq : parentBlock L q ∈ coreBlocks L r B) (hpq : _root_.YangMills.Construction.TorusFields.supDist p q ≤ 1) : False := by
  obtain ⟨p₁, hp₁, a, ha, h1⟩ := mem_coreBlocks_iff_exists.mp hp
  obtain ⟨q₁, hq₁, b, hb, h2⟩ := mem_coreBlocks_iff_exists.mp hq
  have h3 : _root_.YangMills.Construction.TorusFields.supDist p₁ p ≤ L := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq L hp₁
  have h4 : _root_.YangMills.Construction.TorusFields.supDist q q₁ ≤ L := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq L hq₁.symm
  have h5 := hAB a ha b hb
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle a p₁ b
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle p₁ p b
  have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle p q b
  have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle q q₁ b
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm a p₁] at t1
  omega
variable {G γ}
theorem isCoreOf_familyCore (hG : G.IsAdmissibleGround) (hfam : G.IsGasFamily γ)
    (hL : 2 * R.params.side + 1 ≤ 2 * R.range) :
    (G.settingOf γ).IsCoreOf (G.familyCore γ) := by
  classical
  have hst := G.recordsCore hG
  refine ⟨?_, ?_⟩
  · ext b
    show b ∈ G.freeBonds.filter (fun b => γ.fieldAt b = Sum.inl ()) ↔ _
    unfold ChartSetting.freeBondsLeft StepGas.GasGround.freeBonds markedBonds
    simp only [Finset.mem_filter]
    have hnear : _root_.YangMills.Construction.TorusFields.supDist b.1 (b.1 + unitStep (n * R.params.side) b.2) ≤ 1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le _ _
    have hcase : (parentBlock R.params.side b.1 ∈ (G.settingOf γ).storedBlockSet (G.familyCore γ) ∧
        parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈
          (G.settingOf γ).storedBlockSet (G.familyCore γ)) ↔
        G.IsRecorded b ∨ ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds := by
      rw [hst.isRecorded_iff b, mem_storedBlockSet_iff, mem_storedBlockSet_iff]
      constructor
      · rintro ⟨h1 | ⟨θ, hθ, h1⟩, h2 | ⟨θ', hθ', h2⟩⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact (false_of_adjacent_in_far_cores hL (fun a ha c hc => by
            rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
            exact (hfam.1 θ' hθ').far_from_anchor c hc a ha) h1 h2 hnear).elim
        · exact (false_of_adjacent_in_far_cores hL
            (fun a ha c hc => (hfam.1 θ hθ).far_from_anchor a ha c hc) h1 h2 hnear).elim
        · by_cases he : θ = θ'
          · subst he
            exact Or.inr ⟨θ, hθ, mem_coreBonds_iff.mpr ⟨h1, h2⟩⟩
          · exact (false_of_adjacent_in_far_cores hL (hfam.2 θ θ' hθ hθ' he) h1 h2 hnear).elim
      · rintro (⟨h1, h2⟩ | ⟨θ, hθ, hb⟩)
        · exact ⟨Or.inl h1, Or.inl h2⟩
        · obtain ⟨h1, h2⟩ := mem_coreBonds_iff.mp hb
          exact ⟨Or.inr ⟨θ, hθ, h1⟩, Or.inr ⟨θ, hθ, h2⟩⟩
    rw [fieldAt_eq_inl_iff]
    show _ ↔ b ∈ chartBonds R.params.side n ∧ parentBlock R.params.side b.1 ∉ G.cut ∧ _
    rw [hcase]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h1, h2, fun h => h.elim h3 h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨⟨h1, h2⟩, fun h => h3 (Or.inl h)⟩, fun h => h3 (Or.inr h)⟩
  · rcases hG with h | h
    · exact Or.inr ⟨h.cut_eq, h.coarse_cold⟩
    · exact Or.inl ⟨h.isBlockSide, h.cut_eq⟩
theorem frameField_of_not_mem {free : Finset (TorusBond (n * R.params.side))} {V : TorusField n}
    {B : TorusField (n * R.params.side)}
    {b : TorusBond (n * R.params.side)} (h : b ∉ free) : frameField R free V B b.1 b.2 = B b.1 b.2 := by
  classical
  unfold frameField
  exact if_neg h
theorem free_subset_chartBonds : (G.settingWithFamily γ).free ⊆ chartBonds R.params.side n := by apply _root_.YangMills.Construction.InBoxTransfer.free_subset_chartBonds_withFamily <;> assumption
theorem isMarked_familyCore (hG : G.IsAdmissibleGround) (hset : (G.settingOf γ).IsAdmissible) :
    (G.settingOf γ).IsMarked (G.familyCore γ) := by
  classical
  refine ⟨hset.isBaseChoice, fun b hb htree => ?_⟩
  have hst := G.recordsCore hG
  have hnot : ∀ θ, γ.Occupies θ → b ∉ θ.coreBonds := fun θ hθ hs =>
    hb ((mem_storedBlockSet_iff G γ).mpr (Or.inr ⟨θ, hθ, (mem_coreBonds_iff.mp hs).1⟩))
  have hfree : b ∉ (G.settingWithFamily γ).free := fun h => by
    have := free_subset_chartBonds h
    exact (Finset.mem_filter.mp this).2 htree
  show (G.settingWithFamily γ).field 0 b.1 b.2 = 1
  rw [ChartSetting.field_zero, frameField_of_not_mem hfree]
  show (match γ.fieldAt (b.1, b.2) with
    | Sum.inr g => g
    | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2) = 1
  have hf : γ.fieldAt (b.1, b.2) = Sum.inl () :=
    (fieldAt_eq_inl_iff γ).mpr fun ⟨θ, hθ, h⟩ => hnot θ hθ h
  rw [hf]
  show G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 = 1
  unfold CoarseState.fieldWithStoredLinks
  have hnone := hst.markAt_eq_none (parentBlock R.params.side b.1)
    fun h => hb ((mem_storedBlockSet_iff G γ).mpr (Or.inl h))
  rw [hnone]
  rfl
end Membership
section Charts
theorem gaugeAt_congr (hodd : Odd R.params.side) {W W' : TorusField (n * R.params.side)}
    (x : TorusSite (n * R.params.side))
    (hW : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 = parentBlock R.params.side x →
      parentBlock R.params.side (c.1 + unitStep (n * R.params.side) c.2) = parentBlock R.params.side x →
        W c.1 c.2 = W' c.1 c.2) :
    gaugeAt (R := R) W x = gaugeAt (R := R) W' x := by
  obtain ⟨kk, o, ho, hdec⟩ := exists_block_offset hodd (fun i => ((x i).cast : ℤ))
  have hx : x = siteOfInt (blockPoint R.params.side kk o) := by
    funext i
    have := hdec i
    simp only [siteOfInt, blockPoint]
    rw [← this]
    exact (ZMod.intCast_zmod_cast _).symm
  rw [hx] at hW ⊢
  rw [gaugeAt_blockPoint hodd _ kk o ho, gaugeAt_blockPoint hodd _ kk o ho]
  have hc := (BlockOffsets.mem_centredCube_iff o).mp ho
  have key := pathHolonomy_congr (L := R.params.side) W W' (fun i => (R.params.side : ℤ) * kk i)
    (fun i => (R.params.side : ℤ) * kk i) (BlockAverages.axisPath o 1) 0 ?_
  · simpa only [add_zero] using key
  · intro c hcb
    obtain ⟨g1, g2, -⟩ := isAxialBond_of_mem_axisPath hc c hcb
    have hb1 : c.1 ∈ BlockAverages.centredCube R.params.side := (BlockOffsets.mem_centredCube_iff _).mpr g1
    have hb2 : c.1 + Pi.single c.2 1 ∈ BlockAverages.centredCube R.params.side :=
      (BlockOffsets.mem_centredCube_iff _).mpr g2
    have e1 : (siteOfInt ((fun i => (R.params.side : ℤ) * kk i) + c.1) : TorusSite (n * R.params.side)) =
        siteOfInt (blockPoint R.params.side kk c.1) := rfl
    have e2 : (siteOfInt (blockPoint R.params.side kk c.1) : TorusSite (n * R.params.side)) +
        unitStep (n * R.params.side) c.2 =
        siteOfInt (blockPoint R.params.side kk (c.1 + Pi.single c.2 1)) := by
      rw [unitStep_eq_siteOfInt, ← siteOfInt_add]
      congr 1
      funext i
      simp only [blockPoint, Pi.add_apply]
      ring
    rw [e1]
    refine hW (siteOfInt (blockPoint R.params.side kk c.1), c.2) ?_ ?_
    · show parentBlock R.params.side (siteOfInt (blockPoint R.params.side kk c.1) : TorusSite (n * R.params.side)) = _
      rw [parentBlock_blockPoint hodd kk c.1 hb1, parentBlock_blockPoint hodd kk o ho]
    · show parentBlock R.params.side ((siteOfInt (blockPoint R.params.side kk c.1) : TorusSite (n * R.params.side)) +
        unitStep (n * R.params.side) c.2) = _
      rw [e2, parentBlock_blockPoint hodd kk _ hb2, parentBlock_blockPoint hodd kk o ho]
theorem chartCoord_congr (hodd : Odd R.params.side) {W W' : TorusField (n * R.params.side)} (V : TorusField n)
    (b : TorusBond (n * R.params.side))
    (h1 : gaugeAt (R := R) W b.1 = gaugeAt (R := R) W' b.1)
    (h2 : gaugeAt (R := R) W (b.1 + unitStep (n * R.params.side) b.2) =
      gaugeAt (R := R) W' (b.1 + unitStep (n * R.params.side) b.2))
    (h3 : W b.1 b.2 = W' b.1 b.2) : chartCoord R.params V W b = chartCoord R.params V W' b := by
  have hp : ∀ i, (stepBlockFrame R.params.side n).period 0 i = n * R.params.side := fun i => period_zero i
  have hnext : torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1 + BlockAverages.unitStep 0 b.2 =
      torusSiteInFrame (stepBlockFrame R.params.side n) 0 (b.1 + unitStep (n * R.params.side) b.2) := by
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_add hp,
      TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_unitStep hp]
  have hread : ∀ W₀ : TorusField (n * R.params.side),
      readAtLevel (stepBlockFrame R.params.side n) 0 W₀ (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1) b.2 =
        W₀ b.1 b.2 := fun W₀ => TopLevelSites.readAtLevel_torusSiteInFrame hp W₀ b.1 b.2
  have hg : ∀ W₀ : TorusField (n * R.params.side),
      BlockAverages.gaugeTransform (LumpContours.axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) 0 W₀))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W₀) (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1) b.2 =
      gaugeAt (R := R) W₀ b.1 * W₀ b.1 b.2 * (gaugeAt (R := R) W₀ (b.1 + unitStep (n * R.params.side) b.2))⁻¹ := by
    intro W₀
    unfold BlockAverages.gaugeTransform
    rw [hread]
    have t2 : LumpContours.axialGauge (F := stepBlockFrame R.params.side n) 1
        (readAtLevel (stepBlockFrame R.params.side n) 0 W₀)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1 + BlockAverages.unitStep 0 b.2) =
          gaugeAt (R := R) W₀ (b.1 + unitStep (n * R.params.side) b.2) := by
      unfold gaugeAt
      exact congrArg _ hnext
    exact congrArg (fun u => gaugeAt (R := R) W₀ b.1 * W₀ b.1 b.2 * u⁻¹) t2
  unfold chartCoord LumpContours.bondCoordinate
  rw [hg W, hg W', h1, h2, h3]
end Charts
section Components
variable {G : GasGround R n} {γ : GasFamily R n}
theorem lt_supDist_of_rest {θ : GasSupport R n} (hsup : G.IsGasSupport θ)
    (hap : ∀ θ', γ.Occupies θ' → θ' ≠ θ → θ.FarApart θ')
    {a z : TorusSite (n * R.params.side)} (ha : a ∈ θ.sites)
    (hz : z ∈ G.anchorSites ∨ ∃ θ', γ.Occupies θ' ∧ θ' ≠ θ ∧ z ∈ θ'.sites) : 10 * R.range < _root_.YangMills.Construction.TorusFields.supDist a z := by
  rcases hz with hz | ⟨θ', h, hne, hz⟩
  · exact hsup.far_from_anchor a ha z hz
  · exact hap θ' h hne a ha z hz
theorem exists_site_of_mem_blocksNear {L r : ℕ} [NeZero L] {K : Finset (TorusSite (n * L))} {Y : TorusSite n}
    (hY : Y ∈ blocksNear L r K) :
    ∃ p : TorusSite (n * L), parentBlock L p = Y ∧ ∃ a ∈ K, _root_.YangMills.Construction.TorusFields.supDist p a ≤ 5 * r := by
  classical
  obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hY).2
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hp
  obtain ⟨a, ha, hpa⟩ := (mem_thickening _ _ _).mp h2
  exact ⟨p, by simpa [sitesInBlocks] using h1, a, ha, hpa⟩
theorem lt_supDist_of_mem_support {θ : GasSupport R n} (hsup : G.IsGasSupport θ)
    (hap : ∀ θ', γ.Occupies θ' → θ' ≠ θ → θ.FarApart θ')
    {a z : TorusSite (n * R.params.side)} (ha : a ∈ θ.sites) (hz : z ∈ (G.settingOf γ).support) (hzθ : z ∉ θ.2) :
    10 * R.range < _root_.YangMills.Construction.TorusFields.supDist a z := by
  classical
  rcases Finset.mem_union.mp hz with hz | hz
  · exact lt_supDist_of_rest hsup hap ha (Or.inl (Finset.mem_union_right _ hz))
  · obtain ⟨θ', h, hz'⟩ := GasFamily.exists_of_mem_sites hz
    exact lt_supDist_of_rest hsup hap ha (Or.inr ⟨θ', h, fun e => hzθ (e ▸ hz'), Finset.mem_union_right _ hz'⟩)
theorem component_part (hfam : G.IsGasFamily γ) (hr8 : 2 ^ 8 * R.params.side ≤ R.range) (hρ : 0 < R.ballRadius)
    {θ : GasSupport R n} (hθ : γ.Occupies θ) :
    (∃ 𝒦 ⊆ (G.settingOf γ).storedComponents (G.familyCore γ), 𝒦.biUnion id = θ.sites) ∧
      (G.settingOf γ).IsPiece (G.familyCore γ) θ.sites ∧
      (∀ z ∈ (G.settingOf γ).support \ θ.2,
        ∀ y ∈ sitesInBlocks R.params.side (blocksNear R.params.side R.range θ.sites),
        (R.range : ℝ) / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y z) ∧
      (∀ b ∈ (G.familyCore γ).badBonds, b.1 ∈ θ.sites → b ∈ θ.1) ∧
      θ.1.image (fun b => parentBlock R.params.side b.1) ⊆
        badBlocksOff R.params.side (G.familyCore γ).badBonds (G.familyCore γ).core θ.sites ∧
      ((G.settingOf γ).IsAdmissible → ∀ l ∈ torusHotLumps R.params ((G.settingOf γ).field 0),
        l ⊆ θ.sites → l ⊆ θ.2) := by
  classical
  have hsup := hfam.1 θ hθ
  have hap : ∀ θ', γ.Occupies θ' → θ' ≠ θ → θ.FarApart θ' := fun θ' h hne => hfam.2 θ θ' hθ h (Ne.symm hne)
  have hself : ∀ {a}, a ∈ θ.sites → a ∈ G.anchorSites → False := fun ha hb => by
    have := hsup.far_from_anchor _ ha _ hb
    rw [supDist_self] at this
    omega
  have hclass : θ.sites ∈ (G.settingOf γ).storedComponents (G.familyCore γ) := by
    have hsubU : θ.sites ⊆ (G.familyCore γ).badBonds.image Prod.fst ∪ (G.settingOf γ).support ∪
        sitesInBlocks R.params.side (G.familyCore γ).core :=
      fun z hz => (mem_gatheredSites_iff G γ).mpr (Or.inr ⟨θ, hθ, hz⟩)
    unfold ChartSetting.storedComponents clusterComponents
    rw [← Finset.union_sdiff_of_subset hsubU]
    refine self_mem_chainComponents_union_of_separated (fun a ha b hb => ?_) hsup.isCluster.1 hsup.isCluster.2
    obtain ⟨hbU, hbn⟩ := Finset.mem_sdiff.mp hb
    rcases (mem_gatheredSites_iff G γ).mp hbU with h | ⟨θ', h', hz⟩
    · exact lt_supDist_of_rest hsup hap ha (Or.inl h)
    · exact lt_supDist_of_rest hsup hap ha (Or.inr ⟨θ', h', fun e => hbn (e ▸ hz), hz⟩)
  refine ⟨⟨{θ.sites}, by simpa using hclass, by simp⟩, Or.inl ⟨{θ.sites}, ?_, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro X hX
    rw [Finset.mem_singleton] at hX
    subst hX
    refine Finset.mem_filter.mpr ⟨hclass, ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact hself h1 (G.sitesInBlocks_cut_subset_anchorSites h2)
  · intro z hz y hy
    obtain ⟨hzY, hzθ⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨p, hp, a, ha, hpa⟩ := exists_site_of_mem_blocksNear (mem_sitesInBlocks_iff.mp hy)
    have h1 := lt_supDist_of_mem_support hsup hap ha hzY hzθ
    have h2 : _root_.YangMills.Construction.TorusFields.supDist p y ≤ R.params.side := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq _ hp
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle a p z
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle p y z
    rw [supDist_comm a p] at t1
    have h3 : R.range ≤ 4 * _root_.YangMills.Construction.TorusFields.supDist y z := by omega
    have h4 : (R.range : ℝ) ≤ 4 * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) := by exact_mod_cast h3
    linarith
  · intro b hb hb1
    rcases Finset.mem_union.mp hb with h | h
    · exact (hself hb1 (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)))).elim
    · obtain ⟨θ', hθ', hb'⟩ := Finset.mem_biUnion.mp h
      have hh : γ.Occupies θ' := (Finset.mem_filter.mp hθ').2
      by_cases he : θ' = θ
      · exact he ▸ hb'
      · have := hap θ' hh he _ hb1 _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb'))
        rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
        omega
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hs : b.1 ∈ θ.sites := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
    unfold badBlocksOff
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨b.1, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨b,
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ⟩, hb⟩), rfl⟩,
      hs⟩, rfl⟩, ?_⟩
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hsup.bad_subset_free hb)).1).2
  · intro hset l hl hsub z hz
    have hzero : (G.settingOf γ).InBalls 0 := fun b => by
      show coordNorm 0 ≤ R.ballRadius
      have : coordNorm (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
        unfold coordNorm
        have e : (ColdStepAtMirrorFrames.toImaginary 0 : BlockAverages.imaginaryQuaternions) = 0 := by
          apply Subtype.ext
          ext <;> simp [ColdStepAtMirrorFrames.toImaginary]
        rw [e]
        simp
      rw [this]
      exact hρ.le
    have hhull := (hset.isHull 0 hzero).1
    have hzh : z ∈ torusHotSites R.params ((G.settingOf γ).field 0) := Finset.mem_biUnion.mpr ⟨l, hl, hz⟩
    have hzY : z ∈ (G.settingOf γ).support := hhull ((mem_thickening _ _ _).mpr ⟨z, hzh, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩)
    by_contra hzθ
    have := lt_supDist_of_mem_support hsup hap (hsub hz) hzY hzθ
    rw [supDist_self] at this
    omega
end Components
section Insertion
variable {G : GasGround R n} {γ : GasFamily R n}
theorem intCast_mul_eq_of_eq (L : ℕ) [NeZero L] {a b : ℤ} (h : (a : ZMod n) = b) :
    (((L : ℤ) * a : ℤ) : ZMod (n * L)) = (((L : ℤ) * b : ℤ) : ZMod (n * L)) := by apply _root_.YangMills.Construction.CongruentBoxes.intCast_mul_congr <;> assumption
theorem exists_bases_offset_eq_fineSite (s : ChartSetting R n) (hs : s.IsAdmissible) (Y : TorusSite n)
    (h : Fin 4 → ℤ) :
    ∃ o, o ∈ BlockAverages.centredCube R.params.side ∧
      toTorusSite (n * R.params.side) (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
        fineSite R.params.side Y h o := by
  obtain ⟨o, ho, e⟩ := SettingShifts.exists_bases_eq_fineSite s hs (Y + siteOfInt h)
  refine ⟨o, ho, e.trans ?_⟩
  funext i
  simp only [fineSite, siteOfInt]
  rw [Int.cast_add, Int.cast_add]
  refine congrArg (· + ((o i : ℤ) : ZMod (n * R.params.side))) (intCast_mul_eq_of_eq R.params.side ?_)
  push_cast
  simp [siteOfInt]
theorem labelling_insertClass_eq {θ : GasSupport R n} (s : SupportState θ) (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) {z : TorusSite (n * R.params.side)}
    (hθ : z ∉ θ.2)
    (hz : z ∈ (G.settingOf (γ.insertClass θ s)).support) (hz' : z ∈ (G.settingOf γ).support) :
    (G.settingOf (γ.insertClass θ s)).labelling ⟨z, hz⟩ = (G.settingOf γ).labelling ⟨z, hz'⟩ := by
  classical
  have hs' : (γ.insertClass θ s).CoresDisjoint := hs.insertClass hc
  show (if h : z ∈ (γ.insertClass θ s).sites then (γ.insertClass θ s).labelAt h else
      G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right h⟩) =
    (if h : z ∈ γ.sites then γ.labelAt h else G.recordedLabel ⟨z, (Finset.mem_union.mp hz').resolve_right h⟩)
  by_cases hzγ : z ∈ γ.sites
  · have hzs : z ∈ (γ.insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      exact Finset.mem_union_left _ hzγ
    rw [dif_pos hzs, dif_pos hzγ]
    obtain ⟨θ', hh, hzθ⟩ := GasFamily.exists_of_mem_sites hzγ
    have hne : θ' ≠ θ := fun e => hθ (e ▸ hzθ)
    have hh' : (γ.insertClass θ s).Occupies θ' := GasFamily.occupies_insertClass.mpr (Or.inr hh)
    rw [GasFamily.labelAt_eq_of_mem _ hs' hzs hh' hzθ, GasFamily.labelAt_eq_of_mem _ hs hzγ hh hzθ,
      GasFamily.state_insertClass_of_ne hne hh' hh]
  · have hzs : z ∉ (γ.insertClass θ s).sites := by
      rw [GasFamily.sites_insertClass]
      simp [hzγ, hθ]
    rw [dif_neg hzs, dif_neg hzγ]
theorem fine_insertClass_of_mem_coreBonds {θ : GasSupport R n} (s : SupportState θ) (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ θ.coreBonds) :
    (G.settingOf (γ.insertClass θ s)).fine b.1 b.2 = s.1 ⟨b, hb⟩ := by
  classical
  have hfree : b ∉ (G.settingWithFamily (γ.insertClass θ s)).free := by
    rw [G.settingWithFamily_free_insertClass s hs hc]
    intro h
    exact (Finset.mem_filter.mp h).2 hb
  show (G.settingWithFamily (γ.insertClass θ s)).field 0 b.1 b.2 = _
  rw [ChartSetting.field_zero]
  refine (frameField_of_not_mem hfree).trans ?_
  rw [G.settingWithFamily_fine_insertClass s hs hc]
  unfold StepGas.GasGround.baseWithClass
  exact dif_pos hb
theorem chartCoord_insertClass_eq_single (hodd : Odd R.params.side) {θ : GasSupport R n} (s : SupportState θ)
    (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ θ.coreBonds) :
    chartCoord R.params G.coarse (G.settingOf (γ.insertClass θ s)).fine b =
      chartCoord R.params G.coarse (G.frameField (GasFamily.single θ s)) b := by
  have hsame : ∀ c : TorusBond (n * R.params.side), c ∈ θ.coreBonds →
      (G.settingOf (γ.insertClass θ s)).fine c.1 c.2 = G.frameField (GasFamily.single θ s) c.1 c.2 := by
    intro c hc'
    have e1 := fine_insertClass_of_mem_coreBonds (G := G) s hs hc hc'
    have e2 := fine_insertClass_of_mem_coreBonds (G := G) (γ := GasFamily.empty) s (fun θ₁ θ₂ h => by
      simp [GasFamily.Occupies, GasFamily.empty] at h) (fun θ₁ h => by
      simp [GasFamily.Occupies, GasFamily.empty] at h) hc'
    rw [e1]
    exact e2.symm
  obtain ⟨h1, h2⟩ := mem_coreBonds_iff.mp hb
  refine chartCoord_congr hodd G.coarse b (gaugeAt_congr hodd _ fun c e1 e2 => hsame c ?_)
    (gaugeAt_congr hodd _ fun c e1 e2 => hsame c ?_) (hsame b hb)
  · exact mem_coreBonds_iff.mpr ⟨e1 ▸ h1, e2 ▸ h1⟩
  · exact mem_coreBonds_iff.mpr ⟨e1 ▸ h2, e2 ▸ h2⟩
theorem bases_settingOf_congr (γ₁ γ₂ : GasFamily R n) (c : (stepBlockFrame R.params.side n).Cell)
    (h : γ₁.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) =
      γ₂.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) :
    (G.settingOf γ₁).bases c = (G.settingOf γ₂).bases c := by
  show (match γ₁.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
      | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
      | Sum.inl _ => G.groundBases c) =
    (match γ₂.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
      | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
      | Sum.inl _ => G.groundBases c)
  rw [h]
theorem frame_settingOf (γ' : GasFamily R n) (b : TorusBond (n * R.params.side)) :
    (G.settingOf γ').frame b = frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b := rfl
theorem inserted_component_part (hfam : G.IsGasFamily γ) (hr8 : 2 ^ 8 * R.params.side ≤ R.range)
    (hodd : Odd R.params.side) (h2L : 2 ≤ R.params.side)
    (θ : GasSupport R n) (s : SupportState θ) (hsup : G.IsGasSupport θ)
    (hap : ∀ θ', γ.Occupies θ' → θ.FarApart θ')
    (hset : (G.settingOf γ).IsAdmissible) :
    (∀ Y ∈ blocksNear R.params.side R.range θ.sites, (G.settingOf γ).AwayFromCore (G.familyCore γ) Y) ∧
      G.IsGasFamily (γ.insertClass θ s) ∧
      (∀ (Y : TorusSite n) (m : ℕ), (∀ y ∈ θ.core, m + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y Y) → 2 * m + 2 < n →
        SettingsAgreeNear (G.settingOf (γ.insertClass θ s)) (G.settingOf γ) Y Y m) ∧
      ∀ b ∈ θ.coreBonds, chartCoord R.params G.coarse (G.settingOf (γ.insertClass θ s)).fine b =
        chartCoord R.params G.coarse (G.frameField (GasFamily.single θ s)) b := by
  classical
  have hL2 : R.params.side ≤ 2 * R.range := by omega
  have hs : γ.CoresDisjoint := fun θ₁ θ₂ h₁ h₂ y hy₁ hy₂ => by
    by_contra hne
    exact (hfam.2 θ₁ θ₂ h₁ h₂ hne).false_of_mem_cores hL2 hy₁ hy₂
  have hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False := fun θ' h y h1 h2 =>
    (hap θ' h).false_of_mem_cores hL2 h1 h2
  refine ⟨?_, ?_, ?_, fun b hb => chartCoord_insertClass_eq_single hodd s hs hc hb⟩
  · intro Y hY Z hZ y hy z hz
    obtain ⟨p, hp, a, ha, hpa⟩ := exists_site_of_mem_blocksNear hY
    have hyb : parentBlock R.params.side y = Y := by simpa [sitesInBlocks] using hy
    have hzb : parentBlock R.params.side z = Z := by simpa [sitesInBlocks] using hz
    obtain ⟨p', a', hp', hpa', hfar⟩ : ∃ (p' a' : TorusSite (n * R.params.side)),
        parentBlock R.params.side p' = Z ∧ _root_.YangMills.Construction.TorusFields.supDist p' a' ≤ 4 * R.range ∧ 10 * R.range < _root_.YangMills.Construction.TorusFields.supDist a a' := by
      rcases (mem_storedBlockSet_iff G γ).mp hZ with h | ⟨θ', h', hZ'⟩
      · obtain ⟨p', hp', a', ha', h4⟩ := mem_coreBlocks_iff_exists.mp h
        exact ⟨p', a', hp', h4, hsup.far_from_anchor a ha a' ha'⟩
      · obtain ⟨p', hp', a', ha', h4⟩ := GasSupport.mem_core.mp hZ'
        exact ⟨p', a', hp', h4, hap θ' h' a ha a' ha'⟩
    have h1 : _root_.YangMills.Construction.TorusFields.supDist p y ≤ R.params.side := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq _ (hp.trans hyb.symm)
    have h2 : _root_.YangMills.Construction.TorusFields.supDist z p' ≤ R.params.side := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq _ (hzb.trans hp'.symm)
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle a p a'
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle p y a'
    have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z a'
    have t4 := _root_.YangMills.Construction.TorusFields.supDist_triangle z p' a'
    rw [supDist_comm a p] at t1
    have h3 : R.range < 8 * _root_.YangMills.Construction.TorusFields.supDist y z := by omega
    have h4 : (R.range : ℝ) < 8 * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) := by exact_mod_cast h3
    linarith
  · refine ⟨fun θ' h => ?_, fun θ₁ θ₂ h₁ h₂ hne => ?_⟩
    · rcases GasFamily.occupies_insertClass.mp h with e | h
      · exact e ▸ hsup
      · exact hfam.1 θ' h
    · rcases GasFamily.occupies_insertClass.mp h₁ with e₁ | g₁
      · rcases GasFamily.occupies_insertClass.mp h₂ with e₂ | g₂
        · exact absurd (e₁.trans e₂.symm) hne
        · exact e₁ ▸ hap θ₂ g₂
      · rcases GasFamily.occupies_insertClass.mp h₂ with e₂ | g₂
        · exact e₂ ▸ (hap θ₁ g₁).symm
        · exact hfam.2 θ₁ θ₂ g₁ g₂ hne
  · intro Y m hcore hside
    have hbox : ∀ h, OffsetInBox m h → Y + siteOfInt h ∉ θ.core := by
      intro h hh hin
      have h1 := hcore _ hin
      have h2 : _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt h) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y h m fun i => by
        have := hh i
        rw [abs_le] at this
        omega
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
      omega
    have hnear : ∀ q, IsNearIndex R.params.side m q → nearBond R.params.side Y q ∉ θ.coreBonds := by
      intro q hq hin
      apply hbox q.1 hq.1
      have := GasSupport.parentBlock_mem_core_of_mem_coreBonds hin
      rwa [show parentBlock R.params.side (nearBond R.params.side Y q).1 = Y + siteOfInt q.1 from
        parentBlock_fineSite hodd Y q.1 q.2.1 hq.2] at this
    have hfree : ∀ b, b ∉ θ.coreBonds →
        (b ∈ (G.settingWithFamily (γ.insertClass θ s)).free ↔ b ∈ (G.settingWithFamily γ).free) := by
      intro b hb
      rw [G.settingWithFamily_free_insertClass s hs hc]
      simp [hb]
    have hsite : ∀ h o, OffsetInBox m h → o ∈ BlockAverages.centredCube R.params.side →
        fineSite R.params.side Y h o ∉ θ.2 := by
      intro h o hh ho hin
      apply hbox h hh
      have := GasSupport.parentBlock_mem_core_of_mem_sites hin
      rwa [parentBlock_fineSite hodd Y h o ho] at this
    refine ⟨hside, hside, fun _ _ => rfl, fun q hq => hfree _ (hnear q hq), fun q hq hnf => ?_,
      fun q _ _ => (frame_settingOf _ _).trans (frame_settingOf _ _).symm, fun h o hh ho => ?_,
      fun h o hz hz' hh ho => labelling_insertClass_eq s hs hc (hsite h o hh ho) hz hz',
      fun h hh => ?_⟩
    · have hnf₀ : nearBond R.params.side Y q ∉ (G.settingWithFamily γ).free :=
        fun h' => hnf ((hfree _ (hnear q hq)).mpr h')
      show (G.settingWithFamily (γ.insertClass θ s)).field 0 (nearBond R.params.side Y q).1
          (nearBond R.params.side Y q).2 =
        (G.settingWithFamily γ).field 0 (nearBond R.params.side Y q).1 (nearBond R.params.side Y q).2
      have hnf₁ : nearBond R.params.side Y q ∉ (G.settingWithFamily (γ.insertClass θ s)).free := hnf
      rw [ChartSetting.field_zero, ChartSetting.field_zero, frameField_of_not_mem hnf₁, frameField_of_not_mem hnf₀,
        G.settingWithFamily_fine_insertClass s hs hc]
      unfold StepGas.GasGround.baseWithClass
      exact dif_neg (hnear q hq)
    · show fineSite R.params.side Y h o ∈ G.recordedSites ∪ (γ.insertClass θ s).sites ↔
        fineSite R.params.side Y h o ∈ G.recordedSites ∪ γ.sites
      rw [GasFamily.sites_insertClass]
      have := hsite h o hh ho
      simp [this]
    · have hbase : (G.settingOf (γ.insertClass θ s)).bases
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
          (G.settingOf γ).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) := by
        have hcell : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) = Y + siteOfInt h :=
          TopLevelSites.toTorusSite_torusSiteInFrame (fun i => period_one i) _
        refine bases_settingOf_congr _ _ _ ?_
        rw [GasFamily.baseAt_insertClass hs hc, dif_neg (by rw [hcell]; exact hbox h hh)]
      obtain ⟨o, ho, he⟩ := exists_bases_offset_eq_fineSite (G.settingOf γ) hset Y h
      exact ⟨o, ho, hbase ▸ he, he⟩
end Insertion
theorem componentBesideFamily_holds : ComponentBesideFamily := by
  intro R n _ G γ hr8 hρ hodd h2L hG hfam
  have hL : 2 * R.params.side + 1 ≤ 2 * R.range := by omega
  exact ⟨isCoreOf_familyCore hG hfam hL, isMarked_familyCore hG, fun θ hθ => component_part hfam hr8 hρ hθ,
    fun θ s hsup hap hset => inserted_component_part hfam hr8 hodd h2L θ s hsup hap hset⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
