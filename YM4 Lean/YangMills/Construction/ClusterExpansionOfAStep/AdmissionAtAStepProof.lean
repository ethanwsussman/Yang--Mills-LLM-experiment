import YangMills.Construction.ClusterExpansionOfAStep.AdmissionAtAStepForm
import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepCosts BlockPlaces TorusBalls LumpContours
namespace ComponentAdmission
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem frameHotLumpSites_eq_hotLumpsOn (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) :
    frameHotLumpSites ℓ S W = hotLumpsOn ℓ S W := by apply _root_.YangMills.Construction.CongruentAdmission.frameHotLumpSites_eq_hotLumpsOn <;> assumption
theorem curvature_congr {m : ℕ} {W W' : TorusField m} {x : TorusSite m} {μ ν : Fin 4}
    (h1 : W x μ = W' x μ)
    (h2 : W (x + unitStep m μ) ν = W' (x + unitStep m μ) ν)
    (h3 : W (x + unitStep m ν) μ = W' (x + unitStep m ν) μ)
    (h4 : W x ν = W' x ν) : curvature W x μ ν = curvature W' x μ ν := by
  unfold curvature holonomy
  rw [h1, h2, h3, h4]
theorem fieldWithStoredLinks_restrict (q : CoarseState R n) (X : Finset (TorusSite n))
    (W : TorusField (n * R.params.side))
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hx : parentBlock R.params.side x ∈ X) :
    (q.restrict X).fieldWithStoredLinks W x i = q.fieldWithStoredLinks W x i := by
  classical
  simp only [CoarseState.fieldWithStoredLinks, markAt_restrict, if_pos hx]
section Forward
variable (hR : R.ReadsCaseTests) (hLn : R.params.side ∣ n) (V : TorusField n)
  (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
include hR
theorem supDist_parentBlock_le_nextRange {u v : TorusSite (n * R.params.side)}
    (h : supDist u v ≤ 10 * R.range) :
    supDist (parentBlock R.params.side u) (parentBlock R.params.side v) ≤ R.nextRange := by
  have h1 := supDist_parentBlock_le_div_add_one R.params.side u v
  have hL := hR.admissible.L_ge
  have h2 : supDist u v / R.params.side ≤ supDist u v / 16 :=
    Nat.div_le_div_left (by omega) (by norm_num)
  have h3 := hR.range_le
  have h4 := hR.nextRange_ge
  omega
theorem side_le_six_mul_range : R.params.side ≤ 6 * R.range := by
  have := hR.range_ge_side
  omega
include hLn in
theorem restrict_coarseStateOf_isAdmissibleState
    (hbad : bad ⊆ markedBonds R (hotCoreSites R V)) (hW : IsHullState R.params R.range W Yt)
    {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents R.nextRange
      (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V))) :
    ((coarseStateOf R (hotCoreSites R V) W Yt ωt bad b).restrict X).IsAdmissibleCoarseState
      (hotNeighbourhoodOn R X V) X := by
  classical
  have hfit := hR.admissible
  have hr' := hR.nextRange_ge
  have hL6 := side_le_six_mul_range hR
  have hL2 : 2 ≤ R.params.side := by have := hfit.L_ge; omega
  set C := hotCoreSites R V with hC
  set q := coarseStateOf R C W Yt ωt bad b with hq
  set Z := storedBlocks R.params.side R.range bad Yt C with hZ
  set Y₀ := coarseHull R.params.side R.range R.nextRange bad Yt C with hY₀
  set CX := hotNeighbourhoodOn R X V with hCXdef
  have hZY : Z ⊆ Y₀ := storedBlocks_subset_coarseHull C Yt bad
  have hCZ : C ⊆ Z := Finset.subset_union_left
  have hsub : thickening (2 * R.nextRange) (torusHotSites R.params V) ⊆ Y₀ := hCZ.trans hZY
  have hXof : ∀ {y y' : TorusSite n}, y ∈ X → y' ∈ Y₀ → supDist y y' ≤ R.nextRange → y' ∈ X :=
    fun hy hy' h =>
      mem_of_chainConnected_of_mem_chainComponents hX hy hy'
        (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hy) hy' h)
  have hCXiff : ∀ {y}, y ∈ X → (y ∈ CX ↔ y ∈ C) := fun hy =>
    mem_hotNeighbourhoodOn_iff R hfit hLn hr' hsub hX hy
  have hCXsub : CX ⊆ X := hotNeighbourhoodOn_subset R hfit hLn hr' hsub hX
  have hCXC : CX ⊆ C := fun y hy => (hCXiff (hCXsub hy)).mp hy
  have hzone : ∀ {y}, y ∈ (q.restrict X).markedZone ↔ y ∈ Z ∧ y ∈ X := by
    intro y
    rw [mem_controlRegion_restrict, markedZone_coarseStateOf]
  have hlab : ∀ {z}, z ∈ (q.restrict X).labelSet ↔
      (z ∈ Yt ∧ parentBlock R.params.side z ∈ Z) ∧ parentBlock R.params.side z ∈ X := by
    intro z
    rw [mem_labelSet_restrict, mem_labelSet_coarseStateOf]
  have hbadS : ∀ {c : TorusBond (n * R.params.side)}, c ∈ (q.restrict X).storedBadBonds ↔
      (c ∈ bad ∧ parentBlock R.params.side c.1 ∈ Z) ∧ parentBlock R.params.side c.1 ∈ X := by
    intro c
    rw [mem_storedBadBonds_restrict, mem_storedBadBonds_coarseStateOf]
  set T := clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet CX with hT
  have hTmem : ∀ u, u ∈ clusterSites bad Yt C → parentBlock R.params.side u ∈ Z →
      parentBlock R.params.side u ∈ X → u ∈ T := by
    intro u hu hb hx
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem Prod.fst (hbadS.mpr ⟨⟨hc, hb⟩, hx⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hlab.mpr ⟨⟨hu, hb⟩, hx⟩))
    · exact Finset.mem_union_right _
        (mem_sitesInBlocks.mpr ((hCXiff hx).mpr (mem_sitesInBlocks.mp hu)))
  have hTfacts : ∀ u, u ∈ T →
      u ∈ attachedSites R.params.side R.range bad Yt C ∧ parentBlock R.params.side u ∈ X := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨⟨h1, h2⟩, h3⟩ := hbadS.mp hc
        exact ⟨mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL6
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1))) h2, h3⟩
      · obtain ⟨⟨h1, h2⟩, h3⟩ := hlab.mp hu
        exact ⟨mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL6
          (Finset.mem_union_left _ (Finset.mem_union_right _ h1)) h2, h3⟩
    · have h1 := mem_sitesInBlocks.mp hu
      exact ⟨sitesInBlocks_subset_attachedSites R.range bad Yt C
        (mem_sitesInBlocks.mpr (hCXC h1)), hCXsub h1⟩
  have hstep : ∀ {v u}, v ∈ T → u ∈ clusterSites bad Yt C → supDist v u ≤ 10 * R.range → u ∈ T := by
    intro v u hv hu hd
    obtain ⟨h1, h2⟩ := hTfacts v hv
    have h3 := mem_attachedSites_of_supDist_le R.range bad Yt C h1 hu hd
    have h4 := parentBlock_mem_storedBlocks R.range bad Yt C h3
    exact hTmem u hu h4 (hXof h2 (hZY h4) (supDist_parentBlock_le_nextRange hR hd))
  have hpath : ∀ {z u}, z ∈ T → ChainConnected (10 * R.range) (clusterSites bad Yt C) z u →
      u ∈ T ∧ ChainConnected (10 * R.range) T z u := by
    intro z u hz hj
    induction hj with
    | refl => exact ⟨hz, Relation.ReflTransGen.refl⟩
    | tail _ hs ih =>
      have hu := hstep ih.1 hs.2.1 hs.2.2
      exact ⟨hu, ih.2.trans (chainConnected_of_supDist_le ih.1 hu hs.2.2)⟩
  have hatt : attachedSites R.params.side R.range (q.restrict X).storedBadBonds
      (q.restrict X).labelSet CX = T := by
    refine Finset.Subset.antisymm (attachedSites_subset R.range _ _ _) fun z hz => ?_
    obtain ⟨hz1, hz2⟩ := hTfacts z hz
    obtain ⟨X₁, hX₁, hzX₁, c, hc⟩ := (mem_attachedSites_iff R.range bad Yt C).mp hz1
    obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc
    obtain ⟨hcT, hjoin⟩ := hpath hz (chainConnected_of_mem_chainComponents hX₁ hzX₁ hc1)
    have hcX := (hTfacts c hcT).2
    have hcC : c ∈ sitesInBlocks R.params.side CX :=
      mem_sitesInBlocks.mpr ((hCXiff hcX).mpr (mem_sitesInBlocks.mp hc2))
    obtain ⟨X₂, hX₂, hzX₂⟩ := exists_mem_chainComponents (r := 10 * R.range) hz
    exact (mem_attachedSites_iff R.range _ _ _).mpr ⟨X₂, hX₂, hzX₂, c, Finset.mem_inter.mpr
      ⟨mem_of_chainConnected_of_mem_chainComponents hX₂ hzX₂ hcT hjoin, hcC⟩⟩
  have hcore : storedBlocks R.params.side R.range (q.restrict X).storedBadBonds
      (q.restrict X).labelSet CX = (q.restrict X).markedZone := by
    ext y
    rw [hzone]
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact ⟨hCZ (hCXC hy), hCXsub hy⟩
      · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hy).2
        obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
        have hub : parentBlock R.params.side u = y :=
          Finset.mem_singleton.mp (mem_sitesInBlocks.mp hu1)
        rw [hatt] at hu2
        obtain ⟨t, ht, hut⟩ := (mem_thickening _ _ _).mp hu2
        obtain ⟨h1, h2⟩ := hTfacts t ht
        have h3 := parentBlock_mem_storedBlocks_of_near R.range bad Yt C h1 hut
        rw [hub] at h3
        refine ⟨h3, ?_⟩
        have h4 : supDist t u ≤ 10 * R.range := by rw [supDist_comm]; omega
        have h5 := supDist_parentBlock_le_nextRange hR h4
        rw [hub] at h5
        exact hXof h2 (hZY h3) h5
    · rintro ⟨hyZ, hyX⟩
      rcases Finset.mem_union.mp hyZ with hy | hy
      · exact Finset.mem_union_left _ ((hCXiff hyX).mpr hy)
      · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hy).2
        obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
        have hub : parentBlock R.params.side u = y :=
          Finset.mem_singleton.mp (mem_sitesInBlocks.mp hu1)
        obtain ⟨t, ht, hut⟩ := (mem_thickening _ _ _).mp hu2
        have h3 := parentBlock_mem_storedBlocks R.range bad Yt C ht
        have h4 : supDist u t ≤ 10 * R.range := by omega
        have h5 := supDist_parentBlock_le_nextRange hR h4
        rw [hub] at h5
        have htX := hXof hyX (hZY h3) h5
        have htT := hTmem t (attachedSites_subset R.range bad Yt C ht) h3 htX
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ?_⟩)
        rw [hatt]
        exact Finset.mem_inter.mpr ⟨hu1, (mem_thickening _ _ _).mpr ⟨t, htT, hut⟩⟩
  have hstoredW : ∀ (x : TorusSite (n * R.params.side)) (i : Fin 4),
      parentBlock R.params.side x ∈ (q.restrict X).markedZone →
      parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈ (q.restrict X).markedZone →
      (q.restrict X).storedField x i = W x i := by
    intro x i h1 h2
    have h1' := hzone.mp h1
    have h2' := hzone.mp h2
    unfold CoarseState.storedField
    rw [fieldWithStoredLinks_restrict q X _ x i h1'.2]
    exact fieldWithStoredLinks_coarseStateOf C W Yt ωt bad b _ (x, i)
      ((mem_storedFieldBonds_coarseStateOf C W Yt ωt bad b).mpr ⟨h1'.1, h2'.1⟩)
  have hcurv : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4),
      (∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ (q.restrict X).markedZone) →
      curvature (q.restrict X).storedField x μ ν = curvature W x μ ν := by
    intro x μ ν h
    have c1 := h x (by simp [plaquetteVertices])
    have c2 := h (x + unitStep _ μ) (by simp [plaquetteVertices])
    have c3 := h (x + unitStep _ ν) (by simp [plaquetteVertices])
    have c4 := h (x + unitStep _ μ + unitStep _ ν) (by simp [plaquetteVertices])
    have c5 : parentBlock R.params.side (x + unitStep _ ν + unitStep _ μ) ∈
        (q.restrict X).markedZone := by
      rw [add_right_comm]
      exact c4
    exact curvature_congr (hstoredW x μ c1 c2) (hstoredW _ ν c2 c4) (hstoredW _ μ c3 c5)
      (hstoredW x ν c1 c3)
  have hLn' : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hnearlab : ∀ {v u : TorusSite (n * R.params.side)}, v ∈ (q.restrict X).labelSet → u ∈ Yt →
      supDist v u ≤ 10 * R.range → u ∈ (q.restrict X).labelSet := by
    intro v u hv hu hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hlab.mp hv
    have hvθ := mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL6
      (Finset.mem_union_left _ (Finset.mem_union_right _ h1)) h2
    have huS : u ∈ clusterSites bad Yt C := Finset.mem_union_left _ (Finset.mem_union_right _ hu)
    have huθ := mem_attachedSites_of_supDist_le R.range bad Yt C hvθ huS hd
    have hub := parentBlock_mem_storedBlocks R.range bad Yt C huθ
    exact hlab.mpr ⟨⟨hu, hub⟩, hXof h3 (hZY hub) (supDist_parentBlock_le_nextRange hR hd)⟩
  have hr2 : 2 ^ 17 ≤ R.range := by
    have := hR.range_ge_side
    have := hfit.L_ge
    nlinarith
  refine
    { eq_thickening := ?_
      isCore_eq := ?_
      subset_dataZone := fun y hy => hzone.mpr ⟨hCZ (hCXC hy), hCXsub hy⟩
      badBonds_subset := ?_
      fieldBonds_eq := ?_
      attached_eq := hatt
      storedBlocks_eq := hcore
      hotHull_subset := ?_
      component_meets := ?_ }
  · ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hyz⟩ := (mem_thickening _ _ _).mp (subset_of_mem_chainComponents hX hy)
      have hzX : z ∈ X := hXof hy (hZY hz) (by omega)
      exact (mem_thickening _ _ _).mpr ⟨z, hzone.mpr ⟨hz, hzX⟩, hyz⟩
    · intro hy
      obtain ⟨z, hz, hyz⟩ := (mem_thickening _ _ _).mp hy
      obtain ⟨h1, h2⟩ := hzone.mp hz
      have hyY : y ∈ Y₀ := (mem_thickening _ _ _).mpr ⟨z, h1, hyz⟩
      exact hXof h2 hyY (by rw [supDist_comm]; omega)
  · intro y s hs
    rw [markAt_restrict] at hs
    by_cases hyX : y ∈ X
    · rw [if_pos hyX, markAt_coarseStateOf] at hs
      by_cases hyZ : y ∈ storedBlocks R.params.side R.range bad Yt C
      · rw [if_pos hyZ] at hs
        obtain rfl := Option.some.inj hs
        simp only [blockConfigAt, hCXiff hyX]
      · rw [if_neg hyZ] at hs
        cases hs
    · rw [if_neg hyX] at hs
      cases hs
  · intro c hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hbadS.mp hc
    have hm := hbad h1
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, fun h => ?_⟩
    exact (Finset.mem_filter.mp hm).2 (hCXC h)
  · ext c
    rw [mem_storedFieldBonds_restrict, mem_storedFieldBonds_coarseStateOf]
    simp only [bondsOverBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨hzone.mpr ⟨h1, h3⟩, hzone.mpr ⟨h2, hXof h3 (hZY h2) ?_⟩⟩
      have := supDist_parentBlock_le_one hL2 c.1 (c.1 + unitStep (n * R.params.side) c.2)
        (supDist_add_unitStep_le _ _)
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(hzone.mp h1).1, (hzone.mp h2).1⟩, (hzone.mp h1).2⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    rw [frameHotLumpSites_eq_hotLumpsOn] at hl
    obtain ⟨x₀, μ, ν, h1, h2, hcs, c, hc, rfl⟩ := (mem_hotLumpsOn_iff R.params hfit hLn' _ _ _).mp hl
    have hzone' : ∀ w ∈ plaquetteVertices x₀ μ ν,
        parentBlock R.params.side w ∈ (q.restrict X).markedZone := fun w hw =>
      mem_sitesInBlocks.mp (hcs w hw)
    rw [hcurv x₀ μ ν hzone'] at h2
    have hlh : torusLumpOf R.params c ∈ torusHotLumps R.params W :=
      (mem_torusHotLumps_iff R.params hfit hLn' W _).mpr ⟨x₀, μ, ν, h1, h2, c, hc, rfl⟩
    have hcl : c ∈ torusLumpOf R.params c := mem_torusLumpOf_self c
    have hhs : ∀ {w}, w ∈ torusLumpOf R.params c → w ∈ torusHotSites R.params W := fun hw =>
      by rw [torusHotSites, Finset.mem_biUnion]; exact ⟨_, hlh, hw⟩
    have hcY : c ∈ Yt :=
      hW.1 ((mem_thickening _ _ _).mpr ⟨c, hhs hcl, by rw [supDist_self]; omega⟩)
    have hcb := (hzone.mp (hzone' c hc))
    have hcL : c ∈ (q.restrict X).labelSet := hlab.mpr ⟨⟨hcY, hcb.1⟩, hcb.2⟩
    have hzY : z ∈ Yt := hW.1 ((mem_thickening _ _ _).mpr ⟨x, hhs hxl, hzx⟩)
    refine hnearlab hcL hzY ?_
    have h5 := supDist_lt_of_mem_torusHotLumps hfit hLn' hlh hcl hxl
    have h6 := supDist_triangle c x z
    rw [supDist_comm x z] at h6
    omega
  · intro Xc hXc
    obtain ⟨z, hz, rfl⟩ := mem_chainComponents.mp hXc
    have hzY := ((hlab.mp hz).1).1
    obtain ⟨Xt, hXt, hzXt⟩ := exists_mem_chainComponents (r := R.range) hzY
    obtain ⟨l, hl, w, hw⟩ := hW.2 Xt hXt
    obtain ⟨hwl, hwX⟩ := Finset.mem_inter.mp hw
    have hchain : ∀ {u}, ChainConnected R.range Yt z u →
        u ∈ (q.restrict X).labelSet ∧ ChainConnected R.range (q.restrict X).labelSet z u := by
      intro u hj
      induction hj with
      | refl => exact ⟨hz, Relation.ReflTransGen.refl⟩
      | tail _ hs ih =>
        have hu := hnearlab ih.1 hs.2.1 (by omega)
        exact ⟨hu, ih.2.trans (chainConnected_of_supDist_le ih.1 hu hs.2.2)⟩
    obtain ⟨hwL, hjw⟩ := hchain (chainConnected_of_mem_chainComponents hXt hzXt hwX)
    obtain ⟨x₀, μ, ν, h1, h2, c, hc, rfl⟩ := (mem_torusHotLumps_iff R.params hfit hLn' W _).mp hl
    have hcl : c ∈ torusLumpOf R.params c := mem_torusLumpOf_self c
    have hhs : ∀ {u}, u ∈ torusLumpOf R.params c → u ∈ torusHotSites R.params W := fun hu =>
      by rw [torusHotSites, Finset.mem_biUnion]; exact ⟨_, hl, hu⟩
    have hcorner : ∀ u ∈ plaquetteVertices x₀ μ ν, u ∈ (q.restrict X).labelSet := by
      intro u hu
      have hd : supDist u c ≤ 4 := supDist_le_four_of_mem_plaquetteVertices (x₀, μ, ν) hu hc
      have huY : u ∈ Yt := hW.1 ((mem_thickening _ _ _).mpr ⟨c, hhs hcl, by omega⟩)
      refine hnearlab hwL huY ?_
      have h5 := supDist_lt_of_mem_torusHotLumps hfit hLn' hl hwl hcl
      have h6 := supDist_triangle w c u
      rw [supDist_comm c u] at h6
      omega
    have hzone' : ∀ u ∈ plaquetteVertices x₀ μ ν,
        parentBlock R.params.side u ∈ (q.restrict X).markedZone := fun u hu =>
      hzone.mpr ⟨((hlab.mp (hcorner u hu)).1).2, (hlab.mp (hcorner u hu)).2⟩
    refine ⟨torusLumpOf R.params c, ?_, w,
      Finset.mem_inter.mpr ⟨hwl, Finset.mem_filter.mpr ⟨hwL, hjw⟩⟩⟩
    rw [frameHotLumpSites_eq_hotLumpsOn]
    refine (mem_hotLumpsOn_iff R.params hfit hLn' _ _ _).mpr
      ⟨x₀, μ, ν, h1, ?_, fun u hu => mem_sitesInBlocks.mpr (hzone' u hu), c, hc, rfl⟩
    rw [hcurv x₀ μ ν hzone']
    exact h2
end Forward
section Backward
variable (hR : R.ReadsCaseTests) (hLn : R.params.side ∣ n) (V : TorusField n)
  (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
include hR hLn
theorem coarseStateOf_eq_of_isAdmissibleState (q : CoarseState R n)
    (hq : IsHullState R.params R.nextRange V q.1)
    (hadm : ∀ X ∈ chainComponents R.nextRange q.1,
      (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X)
    (hc : q.IsExtension (hotCoreSites R V) W Yt ωt bad b) :
    coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q := by
  classical
  have hfit := hR.admissible
  have hr' := hR.nextRange_ge
  have hL2 : 2 ≤ R.params.side := by have := hfit.L_ge; omega
  set C := hotCoreSites R V with hC
  have hsub : thickening (2 * R.nextRange) (torusHotSites R.params V) ⊆ q.1 := hq.1
  have hexX : ∀ {y}, y ∈ q.1 → ∃ X ∈ chainComponents R.nextRange q.1, y ∈ X := fun hy =>
    exists_mem_chainComponents hy
  have hCXiff : ∀ {X y}, X ∈ chainComponents R.nextRange q.1 → y ∈ X →
      (y ∈ hotNeighbourhoodOn R X V ↔ y ∈ C) :=
    fun hX hy => mem_hotNeighbourhoodOn_iff R hfit hLn hr' hsub hX hy
  have hCXsub : ∀ {X}, X ∈ chainComponents R.nextRange q.1 → hotNeighbourhoodOn R X V ⊆ X :=
    fun hX => hotNeighbourhoodOn_subset R hfit hLn hr' hsub hX
  have hzq : q.markedZone ⊆ q.1 := Finset.filter_subset _ _
  have hCZ : C ⊆ q.markedZone := by
    intro y hy
    obtain ⟨X, hX, hyX⟩ := hexX (hsub hy)
    exact (mem_controlRegion_restrict.mp
      ((hadm X hX).subset_dataZone ((hCXiff hX hyX).mpr hy))).1
  set T₀ := clusterSites q.storedBadBonds q.labelSet C with hT₀
  have hT₀block : ∀ u, u ∈ T₀ → parentBlock R.params.side u ∈ q.markedZone := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hu
        exact ((hc.mem_badBonds_iff c).mp hc').2
      · exact ((hc.mem_support_iff u).mp hu).2
    · exact hCZ (mem_sitesInBlocks.mp hu)
  have hclosed : ∀ {v u}, v ∈ T₀ → u ∈ clusterSites bad Yt C → supDist v u ≤ 10 * R.range →
      u ∈ T₀ := by
    intro v u hv hu hd
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hu
        by_cases hb : parentBlock R.params.side c.1 ∈ q.markedZone
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image_of_mem Prod.fst ((hc.mem_badBonds_iff c).mpr ⟨hc', hb⟩)))
        · have := hc.far_badBonds c hc' hb v hv
          rw [supDist_comm] at this
          omega
      · by_cases hb : parentBlock R.params.side u ∈ q.markedZone
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ ((hc.mem_support_iff u).mpr ⟨hu, hb⟩))
        · have := hc.far_support u hu hb v hv
          rw [supDist_comm] at this
          omega
    · exact Finset.mem_union_right _ hu
  have hTXsubS : ∀ {X}, X ∈ chainComponents R.nextRange q.1 →
      clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet (hotNeighbourhoodOn R X V) ⊆
      clusterSites bad Yt C := by
    intro X hX u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hu
        have h1 := ((hc.mem_badBonds_iff c).mp (mem_storedBadBonds_restrict.mp hc').1).1
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1))
      · have h1 := ((hc.mem_support_iff u).mp (mem_labelSet_restrict.mp hu).1).1
        exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
    · have h1 := mem_sitesInBlocks.mp hu
      exact Finset.mem_union_right _
        (mem_sitesInBlocks.mpr ((hCXiff hX (hCXsub hX h1)).mp h1))
  have hTXsubT : ∀ {X}, X ∈ chainComponents R.nextRange q.1 →
      clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet (hotNeighbourhoodOn R X V) ⊆
      T₀ := by
    intro X hX u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (mem_storedBadBonds_restrict.mp hc').1))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_labelSet_restrict.mp hu).1)
    · have h1 := mem_sitesInBlocks.mp hu
      exact Finset.mem_union_right _
        (mem_sitesInBlocks.mpr ((hCXiff hX (hCXsub hX h1)).mp h1))
  have hTofX : ∀ {X u}, X ∈ chainComponents R.nextRange q.1 → u ∈ T₀ →
      parentBlock R.params.side u ∈ X →
      u ∈ clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet
        (hotNeighbourhoodOn R X V) := by
    intro X u hX hu hb
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (mem_storedBadBonds_restrict.mpr ⟨hc', hb⟩)))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (mem_labelSet_restrict.mpr ⟨hu, hb⟩))
    · exact Finset.mem_union_right _
        (mem_sitesInBlocks.mpr ((hCXiff hX hb).mpr (mem_sitesInBlocks.mp hu)))
  have hatt : attachedSites R.params.side R.range bad Yt C = T₀ := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨X₁, hX₁, hzX₁, c, hc'⟩ := (mem_attachedSites_iff R.range bad Yt C).mp hz
      obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc'
      have hcT : c ∈ T₀ := Finset.mem_union_right _ hc2
      have hj := chainConnected_of_mem_chainComponents hX₁ hc1 hzX₁
      clear hzX₁ hz
      induction hj with
      | refl => exact hcT
      | tail _ hs ih => exact hclosed ih hs.2.1 hs.2.2
    · intro z hz
      obtain ⟨X, hX, hyX⟩ := hexX (hzq (hT₀block z hz))
      have hadmX := hadm X hX
      have hzT := hTofX hX hz hyX
      have hatt' : attachedSites R.params.side R.range (q.restrict X).storedBadBonds
          (q.restrict X).labelSet (hotNeighbourhoodOn R X V) =
          clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet
            (hotNeighbourhoodOn R X V) := hadmX.attached_eq
      rw [← hatt'] at hzT
      obtain ⟨X₂, hX₂, hzX₂, c, hc'⟩ := (mem_attachedSites_iff R.range _ _ _).mp hzT
      obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc'
      have hj := chainConnected_of_mem_chainComponents hX₂ hzX₂ hc1
      have hzS := hTXsubS hX (subset_of_mem_chainComponents hX₂ hzX₂)
      have hmono : ∀ {a b}, ChainConnected (10 * R.range)
          (clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet
            (hotNeighbourhoodOn R X V)) a b →
          ChainConnected (10 * R.range) (clusterSites bad Yt C) a b := by
        intro a b h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hs ih =>
          exact ih.trans (chainConnected_of_supDist_le (hTXsubS hX hs.1) (hTXsubS hX hs.2.1) hs.2.2)
      obtain ⟨X₃, hX₃, hzX₃⟩ := exists_mem_chainComponents (r := 10 * R.range) hzS
      have hcS := hTXsubS hX (subset_of_mem_chainComponents hX₂ hc1)
      have hcC : c ∈ sitesInBlocks R.params.side C := by
        have h1 := mem_sitesInBlocks.mp hc2
        exact mem_sitesInBlocks.mpr ((hCXiff hX (hCXsub hX h1)).mp h1)
      exact (mem_attachedSites_iff R.range bad Yt C).mpr ⟨X₃, hX₃, hzX₃, c,
        Finset.mem_inter.mpr
          ⟨mem_of_chainConnected_of_mem_chainComponents hX₃ hzX₃ hcS (hmono hj), hcC⟩⟩
  have hZ : storedBlocks R.params.side R.range bad Yt C = q.markedZone := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hCZ hy
      · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hy).2
        obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
        rw [hatt] at hu2
        obtain ⟨t, ht, hut⟩ := (mem_thickening _ _ _).mp hu2
        obtain ⟨X, hX, htX⟩ := hexX (hzq (hT₀block t ht))
        have hadmX := hadm X hX
        have htT := hTofX hX ht htX
        have hatt' : attachedSites R.params.side R.range (q.restrict X).storedBadBonds
            (q.restrict X).labelSet (hotNeighbourhoodOn R X V) =
            clusterSites (q.restrict X).storedBadBonds (q.restrict X).labelSet
              (hotNeighbourhoodOn R X V) := hadmX.attached_eq
        rw [← hatt'] at htT
        have hyp : y ∈ storedBlocks R.params.side R.range (q.restrict X).storedBadBonds
            (q.restrict X).labelSet (hotNeighbourhoodOn R X V) :=
          Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
            Finset.mem_inter.mpr ⟨hu1, (mem_thickening _ _ _).mpr ⟨t, htT, hut⟩⟩⟩)
        rw [hadmX.storedBlocks_eq] at hyp
        exact (mem_controlRegion_restrict.mp hyp).1
    · intro hy
      obtain ⟨X, hX, hyX⟩ := hexX (hzq hy)
      have hadmX := hadm X hX
      have hyp : y ∈ (q.restrict X).markedZone := mem_controlRegion_restrict.mpr ⟨hy, hyX⟩
      rw [← hadmX.storedBlocks_eq] at hyp
      rcases Finset.mem_union.mp hyp with h | h
      · exact Finset.mem_union_left _ ((hCXiff hX hyX).mp h)
      · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp h).2
        obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
        rw [hadmX.attached_eq] at hu2
        obtain ⟨t, ht, hut⟩ := (mem_thickening _ _ _).mp hu2
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
          Finset.mem_inter.mpr ⟨hu1, ?_⟩⟩)
        rw [hatt]
        exact (mem_thickening _ _ _).mpr ⟨t, hTXsubT hX ht, hut⟩
  have hY : coarseHull R.params.side R.range R.nextRange bad Yt C = q.1 := by
    ext z
    simp only [coarseHull, hZ]
    constructor
    · intro hz
      obtain ⟨y, hy, hzy⟩ := (mem_thickening _ _ _).mp hz
      obtain ⟨X, hX, hyX⟩ := hexX (hzq hy)
      have hn := (hadm X hX).eq_thickening
      have : z ∈ X := by
        rw [hn]
        exact (mem_thickening _ _ _).mpr ⟨y, mem_controlRegion_restrict.mpr ⟨hy, hyX⟩, hzy⟩
      exact subset_of_mem_chainComponents hX this
    · intro hz
      obtain ⟨X, hX, hzX⟩ := hexX hz
      have hn := (hadm X hX).eq_thickening
      rw [hn] at hzX
      obtain ⟨y, hy, hzy⟩ := (mem_thickening _ _ _).mp hzX
      exact (mem_thickening _ _ _).mpr ⟨y, (mem_controlRegion_restrict.mp hy).1, hzy⟩
  refine coarseState_ext _ _ hY fun y => ?_
  rw [markAt_coarseStateOf]
  by_cases hyZ : y ∈ q.markedZone
  · rw [if_pos (hZ ▸ hyZ)]
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (mem_controlRegion.mp hyZ)
    rw [hs]
    congr 1
    obtain ⟨X, hX, hyX⟩ := hexX (hzq hyZ)
    have hadmX := hadm X hX
    have hps : (q.restrict X).markAt y = some s := by
      rw [markAt_restrict, if_pos hyX, hs]
    refine blockConfig_ext ?_ ?_ ?_ (hc.baseOffset_eq y s hs) ?_
    · have := hadmX.isCore_eq y s hps
      simp only [blockConfigAt, this, hCXiff hX hyX]
    · funext c
      have hb : parentBlock R.params.side (blockSite y c.1 : TorusSite (n * R.params.side)) = y :=
        parentBlock_blockSite y c.1
      have h1 : (blockSite y c.1, c.2) ∈ q.storedBadBonds ↔ s.badBond c = true := by
        rw [mem_storedBadBonds]
        simp only [hb, hs, Option.some.injEq, exists_eq_left', siteOffset_blockSite]
      have h2 := hc.mem_badBonds_iff (blockSite y c.1, c.2)
      simp only [hb, hyZ, and_true] at h2
      simp only [blockConfigAt]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ← h2, h1]
    · funext o
      simp only [blockConfigAt]
      have hb : parentBlock R.params.side (blockSite y o : TorusSite (n * R.params.side)) = y :=
        parentBlock_blockSite y o
      have hl := labelAt_blockSite hs o
      have hset := hc.mem_support_iff (blockSite y o)
      rw [hb] at hset
      by_cases hz : blockSite y o ∈ Yt
      · have hL : blockSite y o ∈ q.labelSet := hset.mpr ⟨hz, hyZ⟩
        rw [dif_pos hz, hc.labeling_eq _ hz hL, ← hl]
        exact (labelAt_eq_inr_labeling q ⟨_, hL⟩).symm
      · have hL : blockSite y o ∉ q.labelSet := fun h => hz (hset.mp h).1
        rw [dif_neg hz, ← hl]
        by_contra h3
        exact hL (mem_labelSet.mpr fun h4 => h3 h4.symm)
    · funext c
      simp only [blockConfigAt]
      have hb : parentBlock R.params.side (blockSite y c.1 : TorusSite (n * R.params.side)) = y :=
        parentBlock_blockSite y c.1
      have hfs : (blockSite y c.1, c.2) ∈ (q.restrict X).storedFieldBonds ↔
          s.linkValue c ≠ Sum.inl () := by
        rw [mem_storedFieldBonds]
        simp only [hb, hps, Option.some.injEq, exists_eq_left', siteOffset_blockSite]
      have hbo : (blockSite y c.1, c.2) ∈ (q.restrict X).storedFieldBonds ↔
          parentBlock R.params.side
            (blockSite (L := R.params.side) y c.1 + unitStep (n * R.params.side) c.2) ∈
            (q.restrict X).markedZone := by
        rw [hadmX.fieldBonds_eq]
        simp only [bondsOverBlocks, Finset.mem_filter, Finset.mem_univ, true_and, hb]
        exact ⟨fun h => h.2, fun h => ⟨mem_controlRegion_restrict.mpr ⟨hyZ, hyX⟩, h⟩⟩
      by_cases hz : parentBlock R.params.side
          (blockSite (L := R.params.side) y c.1 + unitStep (n * R.params.side) c.2) ∈ q.markedZone
      · rw [if_pos (hZ ▸ hz)]
        have hnear : supDist y (parentBlock R.params.side
            (blockSite (L := R.params.side) y c.1 + unitStep (n * R.params.side) c.2)) ≤ 1 := by
          have := supDist_parentBlock_le_one hL2 (blockSite (L := R.params.side) y c.1) _
            (supDist_add_unitStep_le _ c.2)
          rwa [hb] at this
        have hzX : parentBlock R.params.side
            (blockSite (L := R.params.side) y c.1 + unitStep (n * R.params.side) c.2) ∈ X :=
          mem_of_chainConnected_of_mem_chainComponents hX hyX (hzq hz)
            (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hyX) (hzq hz)
              (by omega))
        have hin := hbo.mpr (mem_controlRegion_restrict.mpr ⟨hz, hzX⟩)
        have hne := hfs.mp hin
        rcases hg : s.linkValue c with ⟨⟩ | g
        · exact absurd hg hne
        · have hfield := hc.field_eq _ (mem_storedFieldBonds_restrict.mp hin).1
          simp only at hfield
          rw [hfield]
          simp only [CoarseState.storedField, CoarseState.fieldWithStoredLinks]
          rw [hb, hs, siteOffset_blockSite]
          simp [hg]
      · rw [if_neg (hZ ▸ hz)]
        have hnot : (blockSite y c.1, c.2) ∉ (q.restrict X).storedFieldBonds := fun h =>
          hz (mem_controlRegion_restrict.mp (hbo.mp h)).1
        by_contra h3
        exact hnot (hfs.mpr fun h4 => h3 h4.symm)
  · rw [if_neg (hZ ▸ hyZ)]
    rcases h : q.markAt y with ⟨⟩ | s
    · rfl
    · exact absurd (mem_controlRegion.mpr (by rw [h]; rfl)) hyZ
end Backward
end ComponentAdmission
open ComponentAdmission in
theorem admissionIffComponentTests_holds : AdmissionIffComponentTests := by
  intro R hR n _ hside V q hq W Yt ωt bad b hbad hW
  constructor
  · intro h
    subst h
    exact ⟨fun X hX => restrict_coarseStateOf_isAdmissibleState hR hside.1 V W Yt ωt bad b hbad hW hX,
      coarseStateOf_isExtension _ _ _ _ _ _ (side_le_six_mul_range hR)⟩
  · rintro ⟨h1, h2⟩
    exact coarseStateOf_eq_of_isAdmissibleState hR hside.1 V W Yt ωt bad b q hq h1 h2
end YangMills.Construction.ClusterExpansionOfAStep
end
