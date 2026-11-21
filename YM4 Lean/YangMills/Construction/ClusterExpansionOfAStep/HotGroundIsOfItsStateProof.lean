import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinatesProof
import YangMills.Construction.ClusterExpansionOfAStep.GroundBesideItsLabels
import YangMills.Construction.ClusterExpansionOfAStep.GroundHasWeightAtItsFramesProof
import YangMills.Construction.ClusterExpansionOfAStep.HotGroundIsOfItsState
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepGas StepCosts StepMarks BlockTrees BlockPlaces BlockZones KeptRegion
  TopLevelSites BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters
namespace HotGround
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem sigma_mk_eq_of_eq {α Ω : Type} {Y₁ Y₂ : Finset α} {f : Y₁ → Ω} {g : Y₂ → Ω} (hY : Y₁ = Y₂)
    (h : ∀ z (h₁ : z ∈ Y₁) (h₂ : z ∈ Y₂), f ⟨z, h₁⟩ = g ⟨z, h₂⟩) :
    (⟨Y₁, f⟩ : Σ Y : Finset α, (Y → Ω)) = ⟨Y₂, g⟩ := by
  subst hY
  congr 1
  funext z
  exact h z.1 z.2 z.2
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
variable (G : GasGround R n)
theorem mem_free_iff {b : TorusBond (n * R.params.side)} :
    b ∈ G.groundSetting.free ↔ b ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded b := by apply _root_.YangMills.Construction.GroundWeight.mem_free_settingOf_empty_iff <;> assumption
theorem fine_of_not_mem_free {b : TorusBond (n * R.params.side)} (hb : b ∉ G.groundSetting.free) :
    G.groundSetting.fine b.1 b.2 = G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 := by apply _root_.YangMills.Construction.GroundWeight.fine_of_not_mem_free <;> assumption
theorem bases_eq_groundBases : G.groundSetting.bases = G.groundBases := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.groundSetting_bases <;> assumption
theorem field_zero_eq_fine (hc : G.groundSetting.free ⊆ chartBonds R.params.side n) (hL : Odd R.params.side)
    (hn : 2 ≤ n) : G.groundSetting.field 0 = G.groundSetting.fine := by
  classical
  funext x i
  by_cases hx : (x, i) ∈ G.groundSetting.free
  · have hx' : (x, i) ∈ (G.settingWithFamily GasFamily.empty).free := hx
    have e1 : G.groundSetting.field 0 x i =
        chartLink G.groundSetting x i (G.groundSetting.frame (x, i) +
          toImaginary ((0 : FreeCoords G.groundSetting.free) ⟨(x, i), hx⟩)) := by
      unfold ChartSetting.field
      rw [dif_pos hx]
    have e2 : G.groundSetting.fine x i = chartLink (G.settingWithFamily GasFamily.empty) x i
        ((G.settingWithFamily GasFamily.empty).frame (x, i) +
          toImaginary ((0 : FreeCoords (G.settingWithFamily GasFamily.empty).free) ⟨(x, i), hx'⟩)) := by
      show (G.settingWithFamily GasFamily.empty).field 0 x i = _
      unfold ChartSetting.field
      rw [dif_pos hx']
    rw [e1, e2]
    have htr : ∀ w, gaugeAt G.groundSetting.fine w = gaugeAt (G.settingWithFamily GasFamily.empty).fine w :=
      fun w => blockGauge_field (s := G.settingWithFamily GasFamily.empty) hc hL hn 0 w
    simp only [chartLink, htr]
    rfl
  · exact field_of_not_mem_free (s := G.groundSetting) (b := (x, i)) hx
theorem parentBlock_add_unitStep {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (ht : ¬ IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)) :
    parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) = parentBlock R.params.side x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.FreeChart.parentBlock_add_unitStep <;> assumption
theorem or_rotate (p q r : Prop) : ((p ∨ q) ∨ r) ↔ ((q ∨ r) ∨ p) := by
  tauto
theorem coarseStateOf_congr {C : Finset (TorusSite n)} {W : TorusField (n * R.params.side)}
    {bad : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n}
    {Y₁ Y₂ : Finset (TorusSite (n * R.params.side))} {ω₁ : Y₁ → R.labels.Ω} {ω₂ : Y₂ → R.labels.Ω}
    (h : (⟨Y₁, ω₁⟩ : Σ Y' : Finset (TorusSite (n * R.params.side)), (Y' → R.labels.Ω)) = ⟨Y₂, ω₂⟩) :
    coarseStateOf R C W Y₁ ω₁ bad b = coarseStateOf R C W Y₂ ω₂ bad b := by
  cases h
  rfl
omit [NeZero n] in
theorem blockConfigAt_congr {C Z : Finset (TorusSite n)} {W W' : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))} {b b' : BaseChoice R.params.side n} {y : TorusSite n}
    (hb : baseOffset R b y = baseOffset R b' y)
    (hf : (blockConfigAt R C Z W Yt ωt bad b y).linkValue = (blockConfigAt R C Z W' Yt ωt bad b' y).linkValue) :
    blockConfigAt R C Z W Yt ωt bad b y = blockConfigAt R C Z W' Yt ωt bad b' y := by
  have e : (blockConfigAt R C Z W Yt ωt bad b y).linkValue = (blockConfigAt R C Z W' Yt ωt bad b' y).linkValue := hf
  unfold blockConfigAt at e ⊢
  simp only [hb]
  congr 1
set_option maxHeartbeats 1600000 in
theorem isOverState_of_isHotCase {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) (hf : R.IsWellPosed)
    (hot : G.IsHotCase) (hs : G.groundSetting.IsAdmissible) : G.IsOverState := by
  classical
  have hfit := hf.admissible
  have hodd := hfit.L_odd
  have hσ := hfit.σ_pos
  have hn2 : 2 ≤ n := by
    have h1 := hot.isBlockSide.2
    have h2 := hfit.L_ge
    have h3 := hfit.n₀_ge
    nlinarith
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G (Or.inr hot)
  obtain ⟨W, Yt, ωt, bad, b, hq, hhull, hbsub, hall, hΦ, hmk, hlaw⟩ := hot.exists_state
  have hZs : Z = storedBlocks R.params.side R.range bad Yt G.cut := by
    ext y
    rw [← hZ.recorded_iff y, ← hq, markAt_coarseStateOf]
    by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · simp [hy]
    · simp [hy]
  have hstore : ∀ y, G.state.markAt y =
      if y ∈ Z then some (blockConfigAt R G.cut Z W Yt ωt bad b y) else none := by
    intro y
    rw [hZs, ← hq, markAt_coarseStateOf]
  have hatt := attachedSites_eq_of_subset hall
  have hcore : ∀ z ∈ bad.image Prod.fst ∪ Yt, parentBlock R.params.side z ∈ Z := fun z hz => by
    rw [hZs]
    unfold storedBlocks
    exact Finset.mem_union_right _ (parentBlock_mem_coreBlocks (hall hz))
  have hbad : G.recordedBad = bad := by
    ext c
    unfold GasGround.recordedBad
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hstore]
    constructor
    · rintro ⟨s, hs', hb⟩
      by_cases hy : parentBlock R.params.side c.1 ∈ Z
      · rw [if_pos hy] at hs'
        have := Option.some.inj hs'
        subst this
        unfold blockConfigAt at hb
        simp only [decide_eq_true_eq, BlockPlaces.blockSite_parentBlock_siteOffset] at hb
        exact hb
      · rw [if_neg hy] at hs'
        exact absurd hs' (by simp)
    · intro hc
      have hy : parentBlock R.params.side c.1 ∈ Z :=
        hcore _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
      refine ⟨_, if_pos hy, ?_⟩
      unfold blockConfigAt
      simp only [decide_eq_true_eq, BlockPlaces.blockSite_parentBlock_siteOffset]
      exact hc
  have hlabel : ∀ z (hz : z ∈ Yt), G.state.labelAt z = Sum.inr (ωt ⟨z, hz⟩) := by
    intro z hz
    have hy : parentBlock R.params.side z ∈ Z := hcore _ (Finset.mem_union_right _ hz)
    unfold CoarseState.labelAt
    rw [hstore, if_pos hy]
    simp only [blockConfigAt]
    have hp := BlockPlaces.blockSite_parentBlock_siteOffset (L := R.params.side) z
    have hm' : StepSettings.blockSite (parentBlock R.params.side z) (siteOffset z) ∈ Yt := by rw [hp]; exact hz
    rw [dif_pos hm']
    congr 2
    exact Subtype.ext hp
  have hsites : G.recordedSites = Yt := by
    ext z
    unfold GasGround.recordedSites
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hz
      unfold CoarseState.labelAt at h
      rw [hstore] at h
      by_cases hy : parentBlock R.params.side z ∈ Z
      · rw [if_pos hy] at h
        simp only [blockConfigAt, BlockPlaces.blockSite_parentBlock_siteOffset] at h
        simp [hz] at h
      · rw [if_neg hy] at h
        simp at h
    · intro hz
      rw [hlabel z hz]
      rfl
  have hYt : G.groundSetting.support = Yt := (groundSetting_support G).trans hsites
  have hsig : (⟨G.groundSetting.support, G.groundSetting.labelling⟩ :
      Σ Y' : Finset (TorusSite (n * R.params.side)), (Y' → R.labels.Ω)) = ⟨Yt, ωt⟩ :=
    sigma_mk_eq_of_eq hYt fun z h₁ h₂ =>
      Sum.inr.inj ((labelAt_of_mem_groundSetting_support G z h₁).symm.trans (hlabel z h₂))
  have hval : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 ∈ Z →
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z →
      G.groundSetting.fine c.1 c.2 = W c.1 c.2 := by
    intro c h1 h2
    have hst : G.IsRecorded c := (hZ.bond_iff c).mpr ⟨h1, h2⟩
    have hnf : c ∉ G.groundSetting.free := fun hf' => ((mem_free_iff G).mp hf').2 hst
    rw [fine_of_not_mem_free G hnf]
    unfold CoarseState.fieldWithStoredLinks
    rw [hstore, if_pos h1]
    simp only [blockConfigAt, BlockPlaces.blockSite_parentBlock_siteOffset]
    rw [if_pos h2]
  have hfz := field_zero_eq_fine G hs.subset_chart hodd hn2
  have hUeq : attachedSites R.params.side R.range bad Yt G.cut = KeptRegion.clusterSites R.params.side bad Yt G.cut := by
    rw [hatt]
    ext z
    simp only [KeptRegion.clusterSites, Finset.mem_union]
    exact or_rotate _ _ _
  have hso : G.groundSetting.storedBlockSet G.settingCore = Z := by
    unfold ChartSetting.storedBlockSet
    have h1 : (G.groundSetting.storedComponents G.settingCore).biUnion id =
        attachedSites R.params.side R.range bad Yt G.cut := by
      unfold ChartSetting.storedComponents
      show ((chainComponents (10 * R.range)
        (G.recordedBad.image Prod.fst ∪ G.groundSetting.support ∪ sitesInBlocks R.params.side G.cut))).biUnion id = _
      rw [biUnion_chainComponents, hbad, hYt, hUeq]
      rfl
    rw [h1, hZs]
    rfl
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hzero : G.groundSetting.InBalls 0 := by
    intro c
    have : coordNorm ((0 : FreeCoords G.groundSetting.free) c) = 0 := by
      show ‖((toImaginary (0 : EuclideanSpace ℝ (Fin 3)) : imaginaryQuaternions) : ℍ[ℝ])‖ = 0
      have h0 : ((toImaginary (0 : EuclideanSpace ℝ (Fin 3)) : imaginaryQuaternions) : ℍ[ℝ]) = 0 := by
        ext <;> simp [toImaginary]
      rw [h0, norm_zero]
    rw [this]
    exact hρ.le
  have htr : ∀ x, parentBlock R.params.side x ∈ Z →
      blockGauge R.params.side G.groundSetting.fine x = blockGauge R.params.side W x := by
    intro x hx
    apply blockGauge_congr hodd hn2
    intro z i hb ht
    have h1 : parentBlock R.params.side z ∈ Z := by rw [hb]; exact hx
    exact hval (z, i) h1 (by
      show parentBlock R.params.side (z + TorusFields.unitStep (n * R.params.side) i) ∈ Z
      rw [parentBlock_add_unitStep ht.1]
      exact h1)
  have hchart : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 ∈ Z →
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z →
      chartCoord R.params G.coarse G.groundSetting.fine c = chartCoord R.params G.coarse W c := by
    intro c h1 h2
    rw [chartCoord_eq, chartCoord_eq, htr _ h1, htr _ h2, hval c h1 h2]
  refine ⟨hot, ⟨?_, Or.inl ⟨hot.isBlockSide, hot.cut_eq⟩⟩, ⟨hs.isBaseChoice, ?_⟩, hfz, ?_, ?_, ?_, ?_⟩
  · unfold ChartSetting.freeBondsLeft
    rw [hso]
    ext c
    rw [mem_free_iff G, hZ.bond_iff]
    simp only [markedBonds, Finset.mem_filter]
    exact and_assoc
  · intro c hcZ ht
    rw [hso] at hcZ
    have hnf : c ∉ G.groundSetting.free := not_mem_free_of_isAxialTreeBond hs.subset_chart ht
    rw [fine_of_not_mem_free G hnf]
    unfold CoarseState.fieldWithStoredLinks
    rw [hstore, if_neg hcZ]
    rfl
  · have h0 := hs.isHull 0 hzero
    rwa [hfz] at h0
  · have hb1 : G.groundSetting.bases = G.groundBases := bases_eq_groundBases G
    have s1 : coarseStateOf R G.cut G.groundSetting.fine G.groundSetting.support G.groundSetting.labelling
          G.recordedBad G.groundSetting.bases =
        coarseStateOf R G.cut G.groundSetting.fine Yt ωt bad G.groundSetting.bases := by
      rw [hbad]
      exact coarseStateOf_congr hsig
    rw [s1, ← hq]
    refine coarseState_ext _ _ rfl fun y => ?_
    rw [markAt_coarseStateOf, markAt_coarseStateOf]
    by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt G.cut
    · rw [if_pos hy, if_pos hy]
      have hyZ : y ∈ Z := by rw [hZs]; exact hy
      have hbase : baseOffset R G.groundSetting.bases y = baseOffset R b y := by
        have hgq : G.state.markAt y = some (blockConfigAt R G.cut Z W Yt ωt bad b y) := by
          rw [hstore, if_pos hyZ]
        have hb2 : G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
            frameBlockSite R.params.side n y (baseOffset R b y) := by
          unfold GasGround.groundBases
          have hback : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
              (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y :=
            toTorusSite_torusSiteInFrame (j := 1) BlockOffsets.period_one y
          rw [hback, hgq]
          rfl
        unfold baseOffset
        rw [hb1, hb2]
        unfold frameBlockSite
        rw [toTorusSite_torusSiteInFrame BlockOffsets.period_zero, siteOffset_blockSite]
        rfl
      congr 1
      refine blockConfigAt_congr hbase ?_
      funext p
      by_cases hp : parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y p.1 +
          TorusFields.unitStep (n * R.params.side) p.2) ∈ storedBlocks R.params.side R.range bad Yt G.cut
      · have h2 : parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y p.1 +
            TorusFields.unitStep (n * R.params.side) p.2) ∈ Z := by rw [hZs]; exact hp
        have h1 : parentBlock R.params.side
            (StepSettings.blockSite (L := R.params.side) y p.1 : TorusSite (n * R.params.side)) ∈ Z := by
          rw [parentBlock_blockSite]; exact hyZ
        simp only [blockConfigAt]
        rw [if_pos hp, if_pos hp, hval (StepSettings.blockSite y p.1, p.2) h1 h2]
      · simp only [blockConfigAt]
        rw [if_neg hp, if_neg hp]
    · rw [if_neg hy, if_neg hy]
  · rw [hbad, hYt]
    exact hUeq
  · intro c hc
    rw [hbad] at hc
    have hmk' := hbsub hc
    have hch : c ∈ chartBonds R.params.side n := (Finset.mem_filter.mp hmk').1
    refine ⟨hch, ?_⟩
    have hat : c.1 ∈ attachedSites R.params.side R.range bad Yt G.cut :=
      hall (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
    have h1 : parentBlock R.params.side c.1 ∈ Z :=
      hcore _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
    have h2 : parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z := by
      rw [hZs]
      refine parentBlock_mem_storedBlocks_of_near R.range bad Yt G.cut hat ?_
      have h3 : supDist (c.1 + TorusFields.unitStep (n * R.params.side) c.2) c.1 ≤ 1 := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm, unitStep_eq_siteOfInt]
        exact supDist_add_siteOfInt_le _ _ _ fun i => by
          by_cases hi : i = c.2
          · subst hi; simp
          · simp [hi]
      have h4 := hf.range_ge_base
      omega
    have hst : G.IsRecorded c := (hZ.bond_iff c).mpr ⟨h1, h2⟩
    have hm := hmk c hmk' hst
    rw [if_pos hc] at hm
    by_contra hlt
    push Not at hlt
    apply hm
    have hη : ‖((chartCoord R.params G.coarse W c : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse c : imaginaryQuaternions) : ℍ[ℝ])‖ <
          5 * R.ballRadius / 8 := by
      have e : ((frameDeviation R.params R.anchorRadius R.depth R.frameReach G.groundSetting.coarse
            G.groundSetting.fine c : imaginaryQuaternions) : Quaternion ℝ) =
          ((chartCoord R.params G.coarse W c : imaginaryQuaternions) : ℍ[ℝ]) -
            ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse c : imaginaryQuaternions) : ℍ[ℝ]) := by
        unfold frameDeviation
        show ((chartCoord R.params G.coarse G.groundSetting.fine c -
          frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse c : imaginaryQuaternions) : ℍ[ℝ]) = _
        rw [hchart c h1 h2]
        rfl
      rw [← e]
      exact hlt
    unfold bondMark cutoffFactor
    rw [if_pos (by linarith), hf.isCutoff.vanish_small _ (norm_nonneg _) hη.le]
    simp
end HotGround
theorem hotGroundIsOverState : HotGroundIsOverState :=
  fun _ hf _ _ _ _ hot hs => HotGround.isOverState_of_isHotCase _ hf hot hs
end YangMills.Construction.ClusterExpansionOfAStep
