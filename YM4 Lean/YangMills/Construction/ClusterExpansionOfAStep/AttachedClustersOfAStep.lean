import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts BlockPlaces
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
theorem mem_sitesInBlocks {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by
  simp [sitesInBlocks]
theorem supDist_le_of_parentBlock_eq {u v : TorusSite (n * L)} (h : parentBlock L u = parentBlock L v) :
    supDist u v ≤ L := by
  have hu := blockSite_parentBlock_siteOffset u
  have hv := blockSite_parentBlock_siteOffset v
  rw [h] at hu
  set y := parentBlock L v
  set o := siteOffset u
  set o' := siteOffset v
  have hd : (blockSite y o' : TorusSite (n * L)) =
      blockSite y o + siteOfInt (fun i => ((o' i : ℕ) : ℤ) - ((o i : ℕ) : ℤ)) := by
    funext i
    simp only [blockSite, siteOfInt, Pi.add_apply]
    push_cast
    ring
  rw [← hu, ← hv, hd]
  refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
  have h1 := (o i).2
  have h2 := (o' i).2
  omega
variable (r : ℕ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L))) (C : Finset (TorusSite n))
abbrev clusterSites : Finset (TorusSite (n * L)) := bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C
open Classical in
theorem mem_attachedSites_iff {z : TorusSite (n * L)} :
    z ∈ attachedSites L r bad Yt C ↔
      ∃ X ∈ chainComponents (10 * r) (clusterSites bad Yt C), z ∈ X ∧ (X ∩ sitesInBlocks L C).Nonempty := by
  simp only [attachedSites, clusterComponents, Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨X, ⟨h1, h2⟩, h3⟩
    exact ⟨X, h1, h3, h2⟩
  · rintro ⟨X, h1, h3, h2⟩
    exact ⟨X, ⟨h1, h2⟩, h3⟩
theorem attachedSites_subset : attachedSites L r bad Yt C ⊆ clusterSites bad Yt C := by
  classical
  intro z hz
  obtain ⟨X, hX, hzX, -⟩ := (mem_attachedSites_iff r bad Yt C).mp hz
  exact subset_of_mem_chainComponents hX hzX
theorem sitesInBlocks_subset_attachedSites : sitesInBlocks L C ⊆ attachedSites L r bad Yt C := by
  classical
  intro z hz
  have hzS : z ∈ clusterSites bad Yt C := Finset.mem_union_right _ hz
  obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * r) hzS
  exact (mem_attachedSites_iff r bad Yt C).mpr ⟨X, hX, hzX, z, Finset.mem_inter.mpr ⟨hzX, hz⟩⟩
theorem mem_attachedSites_of_supDist_le {z u : TorusSite (n * L)} (hz : z ∈ attachedSites L r bad Yt C)
    (hu : u ∈ clusterSites bad Yt C) (hd : supDist z u ≤ 10 * r) : u ∈ attachedSites L r bad Yt C := by
  classical
  obtain ⟨X, hX, hzX, hne⟩ := (mem_attachedSites_iff r bad Yt C).mp hz
  exact (mem_attachedSites_iff r bad Yt C).mpr ⟨X, hX,
    mem_of_chainConnected_of_mem_chainComponents hX hzX hu
      (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hzX) hu hd), hne⟩
theorem parentBlock_mem_storedBlocks_of_near {z u : TorusSite (n * L)} (hz : z ∈ attachedSites L r bad Yt C)
    (hd : supDist u z ≤ 4 * r) : parentBlock L u ∈ storedBlocks L r bad Yt C := by
  classical
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ?_⟩)
  exact Finset.mem_inter.mpr ⟨mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr rfl),
    (mem_thickening _ _ _).mpr ⟨z, hz, hd⟩⟩
theorem parentBlock_mem_storedBlocks {z : TorusSite (n * L)} (hz : z ∈ attachedSites L r bad Yt C) :
    parentBlock L z ∈ storedBlocks L r bad Yt C :=
  parentBlock_mem_storedBlocks_of_near r bad Yt C hz (by rw [supDist_self]; omega)
theorem mem_attachedSites_of_parentBlock_mem (hL : L ≤ 6 * r) {u : TorusSite (n * L)}
    (hu : u ∈ clusterSites bad Yt C)
    (hb : parentBlock L u ∈ storedBlocks L r bad Yt C) : u ∈ attachedSites L r bad Yt C := by
  classical
  rcases Finset.mem_union.mp hb with hC | hcore
  · exact sitesInBlocks_subset_attachedSites r bad Yt C (mem_sitesInBlocks.mpr hC)
  · obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hcore).2
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    have hvb : parentBlock L v = parentBlock L u := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hv1)
    obtain ⟨t, ht, hvt⟩ := (mem_thickening _ _ _).mp hv2
    refine mem_attachedSites_of_supDist_le r bad Yt C ht hu ?_
    have h1 := supDist_le_of_parentBlock_eq hvb
    have h2 := supDist_triangle t v u
    rw [supDist_comm t v] at h2
    omega
end Clusters
section Parts
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem markAt_restrict (q : CoarseState R n) (X : Finset (TorusSite n)) (y : TorusSite n) :
    (q.restrict X).markAt y = open Classical in if y ∈ X then q.markAt y else none := by
  classical
  by_cases hX : y ∈ X
  · rw [if_pos hX]
    by_cases hy : y ∈ q.1
    · have hm : y ∈ (q.restrict X).1 := Finset.mem_inter.mpr ⟨hy, hX⟩
      rcases h : q.2 ⟨y, hy⟩ with ⟨⟩ | s
      · rw [markAt_of_inl hy h]
        exact markAt_of_inl (q := q.restrict X) hm h
      · rw [markAt_of_inr hy h]
        exact markAt_of_inr (q := q.restrict X) hm h
    · rw [markAt_of_not_mem hy]
      exact markAt_of_not_mem (q := q.restrict X) fun h => hy (Finset.mem_inter.mp h).1
  · rw [if_neg hX]
    exact markAt_of_not_mem (q := q.restrict X) fun h => hX (Finset.mem_inter.mp h).2
theorem mem_controlRegion {q : CoarseState R n} {y : TorusSite n} : y ∈ q.markedZone ↔ (q.markAt y).isSome := by
  classical
  simp only [CoarseState.markedZone, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  by_contra hy
  rw [markAt_of_not_mem hy] at h
  simp at h
theorem mem_controlRegion_restrict {q : CoarseState R n} {X : Finset (TorusSite n)} {y : TorusSite n} :
    y ∈ (q.restrict X).markedZone ↔ y ∈ q.markedZone ∧ y ∈ X := by
  classical
  rw [mem_controlRegion, mem_controlRegion, markAt_restrict]
  by_cases hX : y ∈ X <;> simp [hX]
theorem labelAt_restrict (q : CoarseState R n) (X : Finset (TorusSite n)) (z : TorusSite (n * R.params.side)) :
    (q.restrict X).labelAt z =
      open Classical in if parentBlock R.params.side z ∈ X then q.labelAt z else Sum.inl () := by
  classical
  simp only [CoarseState.labelAt, markAt_restrict]
  by_cases hX : parentBlock R.params.side z ∈ X <;> simp [hX]
theorem mem_labelSet_restrict {q : CoarseState R n} {X : Finset (TorusSite n)} {z : TorusSite (n * R.params.side)} :
    z ∈ (q.restrict X).labelSet ↔ z ∈ q.labelSet ∧ parentBlock R.params.side z ∈ X := by
  classical
  rw [mem_labelSet, mem_labelSet, labelAt_restrict]
  by_cases hX : parentBlock R.params.side z ∈ X <;> simp [hX]
theorem mem_storedBadBonds {q : CoarseState R n} {c : TorusBond (n * R.params.side)} :
    c ∈ q.storedBadBonds ↔ ∃ s, q.markAt (parentBlock R.params.side c.1) = some s ∧
      s.badBond (siteOffset c.1, c.2) = true := by
  simp [CoarseState.storedBadBonds]
theorem mem_storedBadBonds_restrict {q : CoarseState R n} {X : Finset (TorusSite n)}
    {c : TorusBond (n * R.params.side)} :
    c ∈ (q.restrict X).storedBadBonds ↔ c ∈ q.storedBadBonds ∧ parentBlock R.params.side c.1 ∈ X := by
  classical
  rw [mem_storedBadBonds, mem_storedBadBonds, markAt_restrict]
  by_cases hX : parentBlock R.params.side c.1 ∈ X <;> simp [hX]
theorem mem_storedFieldBonds {q : CoarseState R n} {c : TorusBond (n * R.params.side)} :
    c ∈ q.storedFieldBonds ↔ ∃ s, q.markAt (parentBlock R.params.side c.1) = some s ∧
      s.linkValue (siteOffset c.1, c.2) ≠ Sum.inl () := by
  simp [CoarseState.storedFieldBonds]
theorem mem_storedFieldBonds_restrict {q : CoarseState R n} {X : Finset (TorusSite n)}
    {c : TorusBond (n * R.params.side)} :
    c ∈ (q.restrict X).storedFieldBonds ↔ c ∈ q.storedFieldBonds ∧ parentBlock R.params.side c.1 ∈ X := by
  classical
  rw [mem_storedFieldBonds, mem_storedFieldBonds, markAt_restrict]
  by_cases hX : parentBlock R.params.side c.1 ∈ X <;> simp [hX]
end Parts
section Ext
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coarseState_ext (q q' : CoarseState R n) (h1 : q.1 = q'.1) (h2 : ∀ y, q.markAt y = q'.markAt y) :
    q = q' := by
  obtain ⟨Y, ω⟩ := q
  obtain ⟨Y', ω'⟩ := q'
  simp only at h1
  subst h1
  refine congrArg (Sigma.mk Y) (funext fun y => ?_)
  have h3 := h2 y
  rcases ha : ω y with ⟨⟩ | s
  · rcases hb : ω' y with ⟨⟩ | s'
    · rfl
    · rw [markAt_of_inl (q := ⟨Y, ω⟩) y.2 ha, markAt_of_inr (q := ⟨Y, ω'⟩) y.2 hb] at h3
      cases h3
  · rcases hb : ω' y with ⟨⟩ | s'
    · rw [markAt_of_inr (q := ⟨Y, ω⟩) y.2 ha, markAt_of_inl (q := ⟨Y, ω'⟩) y.2 hb] at h3
      cases h3
    · rw [markAt_of_inr (q := ⟨Y, ω⟩) y.2 ha, markAt_of_inr (q := ⟨Y, ω'⟩) y.2 hb] at h3
      rw [Option.some.inj h3]
end Ext
section Case
variable {R : StepSetup} {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
theorem storedBlocks_subset_coarseHull :
    storedBlocks R.params.side R.range bad Yt C ⊆ coarseHull R.params.side R.range R.nextRange bad Yt C :=
  fun z hz => (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; omega⟩
theorem markAt_coarseStateOf (y : TorusSite n) :
    (coarseStateOf R C W Yt ωt bad b).markAt y = open Classical in
      if y ∈ storedBlocks R.params.side R.range bad Yt C then
        some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) W Yt ωt bad b y) else none := by
  classical
  by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy]
    exact markAt_of_inr (q := coarseStateOf R C W Yt ωt bad b) (storedBlocks_subset_coarseHull C Yt bad hy) (by
      simp only [coarseStateOf, if_pos hy])
  · rw [if_neg hy]
    by_cases hm : y ∈ coarseHull R.params.side R.range R.nextRange bad Yt C
    · exact markAt_of_inl (q := coarseStateOf R C W Yt ωt bad b) hm (by simp only [coarseStateOf, if_neg hy])
    · exact markAt_of_not_mem (q := coarseStateOf R C W Yt ωt bad b) hm
theorem markedZone_coarseStateOf :
    (coarseStateOf R C W Yt ωt bad b).markedZone = storedBlocks R.params.side R.range bad Yt C := by
  classical
  ext y
  rw [mem_controlRegion, markAt_coarseStateOf]
  by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt C <;> simp [hy]
theorem labelAt_coarseStateOf (z : TorusSite (n * R.params.side)) :
    (coarseStateOf R C W Yt ωt bad b).labelAt z = open Classical in
      if h : z ∈ Yt ∧ parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C then
        Sum.inr (ωt ⟨z, h.1⟩) else Sum.inl () := by
  classical
  simp only [CoarseState.labelAt, markAt_coarseStateOf]
  by_cases hb : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C
  · simp only [if_pos hb, blockConfigAt, blockSite_parentBlock_siteOffset]
    by_cases hz : z ∈ Yt
    · simp [hz, hb]
    · simp [hz]
  · simp [hb]
theorem mem_labelSet_coarseStateOf {z : TorusSite (n * R.params.side)} :
    z ∈ (coarseStateOf R C W Yt ωt bad b).labelSet ↔
      z ∈ Yt ∧ parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C := by
  classical
  rw [mem_labelSet, labelAt_coarseStateOf]
  by_cases h : z ∈ Yt ∧ parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C
  · simp [h]
  · simp only [dif_neg h, ne_eq, not_true_eq_false, false_iff]
    exact h
theorem labeling_coarseStateOf (z : TorusSite (n * R.params.side)) (hz : z ∈ Yt)
    (h : z ∈ (coarseStateOf R C W Yt ωt bad b).labelSet) :
    (coarseStateOf R C W Yt ωt bad b).labeling ⟨z, h⟩ = ωt ⟨z, hz⟩ := by
  classical
  have h1 := labelAt_eq_inr_labeling (coarseStateOf R C W Yt ωt bad b) ⟨z, h⟩
  have h2 := labelAt_coarseStateOf C W Yt ωt bad b z
  have h3 := (mem_labelSet_coarseStateOf C W Yt ωt bad b).mp h
  rw [dif_pos h3] at h2
  simp only at h1
  rw [h1] at h2
  exact Sum.inr_injective h2
theorem mem_storedBadBonds_coarseStateOf {c : TorusBond (n * R.params.side)} :
    c ∈ (coarseStateOf R C W Yt ωt bad b).storedBadBonds ↔
      c ∈ bad ∧ parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt C := by
  classical
  rw [mem_storedBadBonds, markAt_coarseStateOf]
  by_cases hb : parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt C
  · simp [hb, blockConfigAt, blockSite_parentBlock_siteOffset]
  · simp [hb]
theorem mem_storedFieldBonds_coarseStateOf {c : TorusBond (n * R.params.side)} :
    c ∈ (coarseStateOf R C W Yt ωt bad b).storedFieldBonds ↔
      parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt C ∧
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
        storedBlocks R.params.side R.range bad Yt C := by
  classical
  rw [mem_storedFieldBonds, markAt_coarseStateOf]
  by_cases hb : parentBlock R.params.side c.1 ∈ storedBlocks R.params.side R.range bad Yt C
  · have e : (blockSite (parentBlock R.params.side c.1) (siteOffset c.1) : TorusSite (n * R.params.side)) = c.1 :=
      blockSite_parentBlock_siteOffset c.1
    rw [if_pos hb]
    constructor
    · rintro ⟨s, hs, hf⟩
      obtain rfl := Option.some.inj hs
      simp only [blockConfigAt] at hf
      rw [e] at hf
      refine ⟨hb, ?_⟩
      by_contra hc
      rw [if_neg hc] at hf
      exact hf rfl
    · rintro ⟨-, hc⟩
      refine ⟨_, rfl, ?_⟩
      simp only [blockConfigAt]
      rw [e, if_pos hc]
      simp
  · simp [hb]
theorem fieldWithStoredLinks_coarseStateOf (W' : TorusField (n * R.params.side)) (c : TorusBond (n * R.params.side))
    (h : c ∈ (coarseStateOf R C W Yt ωt bad b).storedFieldBonds) :
    (coarseStateOf R C W Yt ωt bad b).fieldWithStoredLinks W' c.1 c.2 = W c.1 c.2 := by
  classical
  obtain ⟨h1, h2⟩ := (mem_storedFieldBonds_coarseStateOf C W Yt ωt bad b).mp h
  have e : (blockSite (parentBlock R.params.side c.1) (siteOffset c.1) : TorusSite (n * R.params.side)) = c.1 :=
    blockSite_parentBlock_siteOffset c.1
  simp only [CoarseState.fieldWithStoredLinks, markAt_coarseStateOf, if_pos h1, blockConfigAt]
  rw [e, if_pos h2]
theorem coarseStateOf_isExtension (hL : R.params.side ≤ 6 * R.range) :
    (coarseStateOf R C W Yt ωt bad b).IsExtension C W Yt ωt bad b := by
  classical
  have hstored : ∀ u ∈ (coarseStateOf R C W Yt ωt bad b).storedBadBonds.image Prod.fst ∪
      (coarseStateOf R C W Yt ωt bad b).labelSet ∪ sitesInBlocks R.params.side C,
      u ∈ attachedSites R.params.side R.range bad Yt C := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨h1, h2⟩ := (mem_storedBadBonds_coarseStateOf C W Yt ωt bad b).mp hc
        exact mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1))) h2
      · obtain ⟨h1, h2⟩ := (mem_labelSet_coarseStateOf C W Yt ωt bad b).mp hu
        exact mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL
          (Finset.mem_union_left _ (Finset.mem_union_right _ h1)) h2
    · exact sitesInBlocks_subset_attachedSites R.range bad Yt C hu
  refine
    { field_eq := fun c hc => ?_
      mem_support_iff := fun z => ?_
      labeling_eq := fun z hz hz' => (labeling_coarseStateOf C W Yt ωt bad b z hz hz').symm
      mem_badBonds_iff := fun c => ?_
      baseOffset_eq := fun y s hs => ?_
      far_badBonds := fun c hc hb u hu => ?_
      far_support := fun z hz hb u hu => ?_ }
  · exact (fieldWithStoredLinks_coarseStateOf C W Yt ωt bad b _ c hc).symm
  · rw [markedZone_coarseStateOf]
    exact mem_labelSet_coarseStateOf C W Yt ωt bad b
  · rw [markedZone_coarseStateOf]
    exact mem_storedBadBonds_coarseStateOf C W Yt ωt bad b
  · rw [markAt_coarseStateOf] at hs
    by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt C
    · rw [if_pos hy] at hs
      have := Option.some.inj hs
      rw [← this]
      rfl
    · rw [if_neg hy] at hs
      cases hs
  · rw [markedZone_coarseStateOf] at hb
    by_contra hd
    push Not at hd
    have h1 := mem_attachedSites_of_supDist_le R.range bad Yt C (hstored u hu)
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hc)))
      (by rw [supDist_comm]; exact hd)
    exact hb (parentBlock_mem_storedBlocks R.range bad Yt C h1)
  · rw [markedZone_coarseStateOf] at hb
    by_contra hd
    push Not at hd
    have h1 := mem_attachedSites_of_supDist_le R.range bad Yt C (hstored u hu)
      (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
      (by rw [supDist_comm]; exact hd)
    exact hb (parentBlock_mem_storedBlocks R.range bad Yt C h1)
end Case
end ClusterExpansionOfAStep
end YangMills.Construction
end
