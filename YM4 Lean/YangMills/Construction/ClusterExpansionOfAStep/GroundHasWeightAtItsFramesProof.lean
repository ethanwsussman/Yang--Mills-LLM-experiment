import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettingsProof
import YangMills.Construction.ClusterExpansionOfAStep.NearAFreeBond
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepGas StepSettings StepCosts BlockTrees BlockZones
  FreeBondNeighborhood LumpContours StepFrames
namespace GroundWeight
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem not_occupies_empty (θ : GasSupport R n) : ¬ (GasFamily.empty : GasFamily R n).Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.not_occupies_empty <;> assumption
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
theorem baseAt_empty (y : TorusSite n) : (GasFamily.empty : GasFamily R n).baseAt y = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.baseAt_empty <;> assumption
theorem sites_empty : (GasFamily.empty : GasFamily R n).sites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.sites_empty <;> assumption
theorem isGasFamily_empty : G.IsGasFamily GasFamily.empty :=
  ⟨fun θ h => absurd h (not_occupies_empty θ), fun θ _ h => absurd h (not_occupies_empty θ)⟩
theorem support_settingOf_empty : (G.settingOf GasFamily.empty).support = G.recordedSites := by apply _root_.YangMills.Construction.GasSettings.support_settingOf_empty <;> assumption
theorem mem_free_settingOf_empty_iff {b : TorusBond (n * R.params.side)} :
    b ∈ (G.settingOf GasFamily.empty).free ↔ b ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded b := by
  classical
  constructor
  · intro h
    obtain ⟨h1, h2, _⟩ := mem_free_settingOf h
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    show b ∈ G.freeBonds.filter fun b => (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl ()
    unfold GasGround.freeBonds
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, h2⟩, fieldAt_empty b⟩
theorem fine_settingWithFamily_empty (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    (G.settingWithFamily GasFamily.empty).fine x i = G.state.fieldWithStoredLinks (trivialField _) x i := by
  show (match (GasFamily.empty : GasFamily R n).fieldAt (x, i) with
    | Sum.inr g => g
    | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) x i) = _
  rw [fieldAt_empty]
theorem fine_of_not_mem_free {b : TorusBond (n * R.params.side)} (hb : b ∉ (G.settingOf GasFamily.empty).free) :
    (G.settingOf GasFamily.empty).fine b.1 b.2 = G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 := by
  classical
  show (G.settingWithFamily GasFamily.empty).field 0 b.1 b.2 = _
  have hb' : (b.1, b.2) ∉ (G.settingWithFamily GasFamily.empty).free := hb
  unfold ChartSetting.field
  rw [dif_neg hb']
  exact fine_settingWithFamily_empty b.1 b.2
theorem getRight_eq_of_eq_inr {α : Type} {m : WithNone α} {a : α} (h : m = Sum.inr a) (h' : m.isRight = true) :
    m.getRight h' = a := by
  subst h
  rfl
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ} {Z S : Finset (TorusSite n)} {s₀ : ℝ}
section Main
variable (hS : StepHypotheses R δ lam σA cg N G GasFamily.empty Z S s₀)
include hS
theorem mem_anchorSites_of_mem_bad {c : TorusBond (n * R.params.side)} (hc : c ∈ (G.settingOf GasFamily.empty).bad) :
    c.1 ∈ G.anchorSites := by
  classical
  have h1 : c ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => (GasFamily.empty : GasFamily R n).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut := hc
  simp only [Finset.mem_union] at h1
  unfold GasGround.anchorSites
  rcases h1 with (h | h) | h
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
  · obtain ⟨θ, hθ, _⟩ := Finset.mem_biUnion.mp h
    exact absurd (Finset.mem_filter.mp hθ).2 (not_occupies_empty θ)
  · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    unfold sitesInBlocks
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
theorem deviation_le_of_not_mem_anchorSites (hm : NonzeroMarksOffFree G GasFamily.empty 0)
    {b' : TorusBond (n * R.params.side)} (hc : b' ∈ chartBonds R.params.side n)
    (hat : b'.1 ∉ G.anchorSites) :
    ‖((chartCoord R.params G.coarse ((G.settingOf GasFamily.empty).field 0) b' : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b' : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        R.ballRadius := by
  by_cases hf : b' ∈ (G.settingOf GasFamily.empty).free
  · exact deviation_le_of_mem_free hS 0 (inBalls_zero hS) ⟨b', hf⟩
  · exact (deviation_lt_of_not_mem_free hS hm 0 hc hf fun hb => hat (mem_anchorSites_of_mem_bad hS hb)).le
theorem curvature_lt_of_corner_off_zone (hGood : coldPlaquette_of_small_frameDeviation)
    (hm : NonzeroMarksOffFree G GasFamily.empty 0)
    {x : TorusSite (n * R.params.side)} {μ ν : Fin 4} (hμ : μ < ν) {z₀ : TorusSite (n * R.params.side)}
    (hz₀ : z₀ ∈ plaquetteVertices x μ ν) (hZ : parentBlock R.params.side z₀ ∉ Z) :
    curvature ((G.settingOf GasFamily.empty).field 0) x μ ν < R.params.threshold / 4 := by
  classical
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  have hoff : ∀ u, supDist z₀ u ≤ 4 * R.range → u ∉ G.anchorSites := fun u hu hat => by
    apply hZ
    rw [hS.markedZone.zone_eq]
    exact Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near hat hu)
  have hclose : ∀ z ∈ plaquetteVertices x μ ν, supDist z₀ z ≤ 4 := fun z hz => by
    have h1 := supDist_le_two_of_mem_plaquetteVertices hz₀
    have h2 := supDist_le_two_of_mem_plaquetteVertices hz
    have h3 := supDist_triangle z₀ x z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z₀ x] at h3
    omega
  refine hGood R.params δ lam R.anchorRadius σA cg N hS.admissible hS.chainConstants hS.two_threshold_le R.depth
    R.range R.nextRange n G.coarse S G.cut s₀ hS.rangesAdmissible hS.situation hS.decay_gap
    _ x μ ν hμ ?_ ?_
  · intro z hz hzC
    refine hoff z (by have := hclose z hz; omega) ?_
    unfold GasGround.anchorSites
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    unfold sitesInBlocks
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzC⟩
  · rintro b' hc ⟨z, hz, hbz⟩
    have h1 := supDist_le_of_parentBlock_eq hbz
    have h2 := hclose z hz
    have h3 := supDist_triangle z₀ z b'.1
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z b'.1] at h3
    exact deviation_le_of_not_mem_anchorSites hS hm hc (hoff _ (by omega))
theorem exists_parentBlock_eq (y₀ : TorusSite n) :
    ∃ u : TorusSite (n * R.params.side), parentBlock R.params.side u = y₀ := by
  obtain ⟨u, hu⟩ := torusSiteInFrame_surjective (m := n * R.params.side) (stepBlockFrame R.params.side n) 0
    stepBlockFrame_period_zero
    (cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀))
  refine ⟨u, ?_⟩
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube ((stepBlockFrame R.params.side n).blockSide ^
      ((stepBlockFrame R.params.side n).top - 0)) := by
    apply mem_centredCube_top
    rw [_root_.YangMills.Construction.BlockTrees.mem_centredCube_iff]
    intro i
    have : 0 < (stepBlockFrame R.params.side n).blockSide := (side_odd hS).pos
    simp
    omega
  have h1 := BlockTrees.enclosingCell_cellCentre_add (F := stepBlockFrame R.params.side n) (side_odd hS) (j := 0)
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) 0 h0
  rw [siteOfCoords_zero, add_zero, ← hu, enclosingCell_torusSiteInFrame] at h1
  exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one h1
theorem nearbyLumps_eq_empty_off_zone (hcorner : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
      R.params.threshold ≤ curvature ((G.settingOf GasFamily.empty).field 0) x μ ν →
        ∀ z ∈ plaquetteVertices x μ ν, z ∈ G.anchorSites)
    (y₀ : TorusSite n) (hy : y₀ ∉ Z) :
    nearbyLumps (stepHotLumps R.params ((G.settingOf GasFamily.empty).field 0))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) = ∅ := by
  classical
  have hodd := side_odd hS
  have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hodd
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => by
    have := hS.two_le
    show 0 < n
    omega
  have hfar := hS.side_le_range
  apply Finset.eq_empty_of_forall_notMem
  intro l hlm
  obtain ⟨p, hpc, hhot, x, hx, hu⟩ := exists_hot_corner_of_mem_nearbyLumps (F := stepBlockFrame R.params.side n)
    R.params.grid hodd hodd' hs R.params.threshold _ _ _ l hlm
  obtain ⟨h, hh, hcell⟩ := Finset.mem_image.mp hu
  obtain ⟨x₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero p₀
  have hμν : μ < ν := lt_of_mem_cutPlaquettes hpc
  have hhot' : R.params.threshold ≤ curvature ((G.settingOf GasFamily.empty).field 0) p₁ μ ν :=
    le_of_le_of_eq hhot (plaquetteDefect_readAtLevel_zero _ p₁ μ ν)
  have hcn : x₁ ∈ plaquetteVertices p₁ μ ν := mem_plaquetteVertices_of_mem_plaquetteCorners hx
  have hat := hcorner p₁ μ ν hμν hhot' x₁ hcn
  have hblock : parentBlock R.params.side x₁ = y₀ + siteOfInt h := by
    have h1 := hcell.trans (enclosingCell_torusSiteInFrame x₁)
    exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
      (h1.symm.trans (torusSiteInFrame_one_add_siteOfCoords y₀ h))
  have hdist : supDist y₀ (parentBlock R.params.side x₁) ≤ 2 := by
    rw [hblock]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc] at this
    norm_num at this
    omega
  obtain ⟨u, hu'⟩ := exists_parentBlock_eq hS y₀
  have d2 := supDist_le_of_parentBlock u x₁
  rw [hu'] at d2
  have d5 : R.params.side * (supDist y₀ (parentBlock R.params.side x₁) + 2) ≤ R.params.side * 4 :=
    Nat.mul_le_mul_left _ (by omega)
  apply hy
  rw [hS.markedZone.zone_eq, ← hu']
  exact Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near hat (by omega))
theorem bases_settingOf_empty : (G.settingOf GasFamily.empty).bases = G.groundBases := by
  funext c
  show (match (GasFamily.empty : GasFamily R n).baseAt
      (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [baseAt_empty]
omit hS in
theorem baseLaw_ne_zero_of_mem {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (h : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    baseLaw (R := R) W b ≠ 0 := by
  classical
  unfold baseLaw
  rw [if_pos h]
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h))
theorem toTorusSite_torusSiteInFrame (y₀ : TorusSite n) :
    toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) = y₀ := by
  funext k
  exact intCast_cast_intCast_cast (stepBlockFrame_period_one k).symm (y₀ k)
theorem hasWeightAt_empty_of_cold (hGood : coldPlaquette_of_small_frameDeviation) (hc : G.IsColdCase) :
    G.HasWeightAt GasFamily.empty 0 := by
  classical
  have hσ := hS.admissible.σ_pos
  have hstore : ∀ y, G.state.markAt y = none := by
    intro y
    unfold CoarseState.markAt
    rw [dif_neg]
    rw [hc.state_empty]
    simp
  have hZe : Z = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    have := (hS.markedZone.recorded_iff y).mpr hy
    simp [hstore] at this
  have hsites : G.recordedSites = ∅ := by
    unfold GasGround.recordedSites CoarseState.labelAt
    simp [hstore]
  have hYt : (G.settingOf GasFamily.empty).support = ∅ := support_settingOf_empty.trans hsites
  have hm : NonzeroMarksOffFree G GasFamily.empty 0 := by
    intro b hb hnf _
    exfalso
    apply hnf
    refine mem_free_settingOf_empty_iff.mpr ⟨Finset.mem_filter.mpr ⟨hb, by rw [hc.cut_eq]; simp⟩, ?_⟩
    unfold GasGround.IsRecorded
    simp [hstore]
  have hno : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
      ¬ R.params.threshold ≤ curvature ((G.settingOf GasFamily.empty).field 0) x μ ν := by
    intro x μ ν hμ h
    have h1 := curvature_lt_of_corner_off_zone hS hGood hm (x := x) hμ (z₀ := x)
      (by simp [plaquetteVertices]) (by simp [hZe])
    linarith
  have hhot : torusHotLumps R.params ((G.settingOf GasFamily.empty).field 0) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro l hl
    obtain ⟨x, μ, ν, hμ, h, _⟩ := (mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS) _ l).mp hl
    exact hno x μ ν hμ h
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
  · have := ballRadius_pos hS
    simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using this
  · unfold IsHullState torusHotSites
    rw [hhot, hYt]
    simp [chainComponents, thickening]
  · intro X hX
    rw [hYt] at hX
    simp [chainComponents] at hX
  · rw [bases_settingOf_empty hS]
    apply baseLaw_ne_zero_of_mem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => ?_⟩
    obtain ⟨y₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one y
    have hb := nearbyLumps_eq_empty_off_zone hS (fun x μ ν hμ h => absurd h (hno x μ ν hμ)) y₀ (by simp [hZe])
    have hcen : G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) =
        cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) := by
      unfold GasGround.groundBases
      rw [hstore]
    exact ⟨fun _ => hcen, fun h => absurd (Or.inl hb) h⟩
  · intro b _ hnf _
    exact hm b ‹_› hnf ‹_›
omit hS in
theorem enclosingCell_cellCentre {F : BlockFrame} (hL : Odd F.blockSide) (y : F.Cell) :
    enclosingCell (cellCentre F.depth y : F.Site F.depth) = y := by
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube (F.blockSide ^ (F.top - F.depth)) := by
    apply mem_centredCube_top
    rw [_root_.YangMills.Construction.BlockTrees.mem_centredCube_iff]
    intro i
    have := hL.pos
    simp
    omega
  have h1 := BlockTrees.enclosingCell_cellCentre_add hL y 0 h0
  rwa [siteOfCoords_zero, add_zero] at h1
omit hS in
theorem parentBlock_add_unitStep (hL : Odd R.params.side) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (ht : ¬ IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)) :
    parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) = parentBlock R.params.side x := by
  have h1 : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x +
      BlockAverages.unitStep (F := stepBlockFrame R.params.side n) 0 i) =
      enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x) := not_not.mp ht
  rw [← torusSiteInFrame_unitStep, ← torusSiteInFrame_add] at h1
  exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
    ((enclosingCell_torusSiteInFrame _).symm.trans (h1.trans (enclosingCell_torusSiteInFrame x)))
theorem hasWeightAt_empty_of_hot (hGood : coldPlaquette_of_small_frameDeviation)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hh : G.IsHotCase) :
    G.HasWeightAt GasFamily.empty 0 := by
  classical
  have hσ := hS.admissible.σ_pos
  have hodd := side_odd hS
  have hn := hS.two_le
  have hZ := hS.markedZone
  obtain ⟨W, Yt, ωt, bad, b, hq, hhull, hbsub, hall, hΦ, hmk, hlaw⟩ := hh.exists_state
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
  have hcore : ∀ z ∈ bad.image Prod.fst ∪ Yt, parentBlock R.params.side z ∈ Z := fun z hz => by
    rw [hZs]
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
        simp only [decide_eq_true_eq, blockSite_parentBlock_siteOffset] at hb
        exact hb
      · rw [if_neg hy] at hs
        exact absurd hs (by simp)
    · intro hc
      have hy : parentBlock R.params.side c.1 ∈ Z :=
        hcore _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
      refine ⟨_, if_pos hy, ?_⟩
      unfold blockConfigAt
      simp only [decide_eq_true_eq, blockSite_parentBlock_siteOffset]
      exact hc
  have hlabel : ∀ z (hz : z ∈ Yt), G.state.labelAt z = Sum.inr (ωt ⟨z, hz⟩) := by
    intro z hz
    have hy : parentBlock R.params.side z ∈ Z := hcore _ (Finset.mem_union_right _ hz)
    unfold CoarseState.labelAt
    rw [hstore, if_pos hy]
    simp only [blockConfigAt]
    have hp := blockSite_parentBlock_siteOffset (L := R.params.side) z
    have hm' : blockSite (parentBlock R.params.side z) (siteOffset z) ∈ Yt := by rw [hp]; exact hz
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
        simp only [blockConfigAt, blockSite_parentBlock_siteOffset] at h
        simp [hz] at h
      · rw [if_neg hy] at h
        simp at h
    · intro hz
      rw [hlabel z hz]
      rfl
  have hYt : (G.settingOf GasFamily.empty).support = Yt := support_settingOf_empty.trans hsites
  have hatY : ∀ z ∈ Yt, z ∈ G.anchorSites := fun z hz => by
    unfold GasGround.anchorSites
    rw [hsites]
    exact Finset.mem_union_right _ hz
  have hval : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 ∈ Z →
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z →
      (G.settingOf GasFamily.empty).field 0 c.1 c.2 = W c.1 c.2 := by
    intro c h1 h2
    have hst : G.IsRecorded c := (hZ.bond_iff c).mpr ⟨h1, h2⟩
    have hnf : c ∉ (G.settingOf GasFamily.empty).free := fun hf => (mem_free_settingOf_empty_iff.mp hf).2 hst
    rw [field_of_not_mem_free hnf, fine_of_not_mem_free hnf]
    unfold CoarseState.fieldWithStoredLinks
    rw [hstore, if_pos h1]
    simp only [blockConfigAt, blockSite_parentBlock_siteOffset]
    rw [if_pos h2]
  have htr : ∀ x, parentBlock R.params.side x ∈ Z →
      blockGauge R.params.side ((G.settingOf GasFamily.empty).field 0) x = blockGauge R.params.side W x := by
    intro x hx
    apply blockGauge_congr hodd hn
    intro z i hb ht
    have h1 : parentBlock R.params.side z ∈ Z := by rw [hb]; exact hx
    exact hval (z, i) h1 (by
      show parentBlock R.params.side (z + TorusFields.unitStep (n * R.params.side) i) ∈ Z
      rw [parentBlock_add_unitStep hodd ht.1]
      exact h1)
  have hchart : ∀ c : TorusBond (n * R.params.side), parentBlock R.params.side c.1 ∈ Z →
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z →
      chartCoord R.params G.coarse ((G.settingOf GasFamily.empty).field 0) c = chartCoord R.params G.coarse W c := by
    intro c h1 h2
    rw [chartCoord_eq, chartCoord_eq, htr _ h1, htr _ h2, hval c h1 h2]
  have hmarkW : ∀ c ∈ chartBonds R.params.side n, c ∉ (G.settingOf GasFamily.empty).free →
      c ∉ (G.settingOf GasFamily.empty).bad → G.IsRecorded c ∧ bondMark R G.coarse W c ≠ 0 := by
    intro c hc hnf hnb
    have hC : parentBlock R.params.side c.1 ∉ G.cut := fun hC => hnb (by
      show c ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => (GasFamily.empty : GasFamily R n).Occupies θ).biUnion
        Prod.fst ∪ (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, hC⟩))
    have hmk' : c ∈ markedBonds R G.cut := Finset.mem_filter.mpr ⟨hc, hC⟩
    have hst : G.IsRecorded c := by
      by_contra hn'
      exact hnf (mem_free_settingOf_empty_iff.mpr ⟨hmk', hn'⟩)
    have hcb : c ∉ bad := fun hcb => hnb (by
      show c ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => (GasFamily.empty : GasFamily R n).Occupies θ).biUnion
        Prod.fst ∪ (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
      rw [hbad]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hcb))
    have := hmk c hmk' hst
    rw [if_neg hcb] at this
    exact ⟨hst, this⟩
  have hm : NonzeroMarksOffFree G GasFamily.empty 0 := by
    intro c hc hnf hnb
    obtain ⟨hst, hmW⟩ := hmarkW c hc hnf hnb
    obtain ⟨h1, h2⟩ := (hZ.bond_iff c).mp hst
    unfold bondMark at hmW ⊢
    rw [hchart c h1 h2]
    exact hmW
  have hsame : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4),
      (∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ Z) →
      curvature ((G.settingOf GasFamily.empty).field 0) x μ ν = curvature W x μ ν := by
    intro x μ ν hz
    have c1 : parentBlock R.params.side x ∈ Z := hz x (by simp [plaquetteVertices])
    have c2 : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) μ) ∈ Z :=
      hz _ (by simp [plaquetteVertices])
    have c3 : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) ν) ∈ Z :=
      hz _ (by simp [plaquetteVertices])
    have c4 : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) μ +
        TorusFields.unitStep (n * R.params.side) ν) ∈ Z := hz _ (by simp [plaquetteVertices])
    have c5 : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) ν +
        TorusFields.unitStep (n * R.params.side) μ) ∈ Z := by
      rw [add_right_comm]
      exact c4
    unfold curvature holonomy
    rw [hval (x, μ) c1 c2, hval (x, ν) c1 c3, hval (x + TorusFields.unitStep (n * R.params.side) μ, ν) c2 c4,
      hval (x + TorusFields.unitStep (n * R.params.side) ν, μ) c3 c5]
  have hWcorner : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
      R.params.threshold ≤ curvature W x μ ν → ∀ z ∈ plaquetteVertices x μ ν, z ∈ Yt := by
    intro x μ ν hμ hh' z hz
    have hl : torusLumpOf R.params z ∈ torusHotLumps R.params W :=
      (mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS) W _).mpr ⟨x, μ, ν, hμ, hh', z, hz, rfl⟩
    have hs : z ∈ torusHotSites R.params W := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self z⟩
    exact hhull.1 ((mem_thickening _ _ _).mpr ⟨z, hs, by rw [supDist_self]; exact Nat.zero_le _⟩)
  have hHP : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
      (R.params.threshold ≤ curvature ((G.settingOf GasFamily.empty).field 0) x μ ν ↔
        R.params.threshold ≤ curvature W x μ ν) := by
    intro x μ ν hμ
    constructor
    · intro h
      have hz : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ Z := by
        intro z hz
        by_contra hn'
        have := curvature_lt_of_corner_off_zone hS hGood hm hμ hz hn'
        linarith
      rw [hsame x μ ν hz] at h
      exact h
    · intro h
      have hz : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ Z := fun z hz =>
        hcore z (Finset.mem_union_right _ (hWcorner x μ ν hμ h z hz))
      rw [hsame x μ ν hz]
      exact h
  have hhot : torusHotLumps R.params ((G.settingOf GasFamily.empty).field 0) = torusHotLumps R.params W := by
    ext l
    rw [mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS),
      mem_torusHotLumps_iff R.params hS.admissible (side_dvd hS)]
    constructor
    · rintro ⟨x, μ, ν, hμ, h, hl⟩
      exact ⟨x, μ, ν, hμ, (hHP x μ ν hμ).mp h, hl⟩
    · rintro ⟨x, μ, ν, hμ, h, hl⟩
      exact ⟨x, μ, ν, hμ, (hHP x μ ν hμ).mpr h, hl⟩
  have hlumps : hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
      (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf GasFamily.empty).field 0)) =
      hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
    refine FreeBondNeighborhood.hotLumps_congr _ _ _ _ _ fun p hp => ?_
    obtain ⟨x, μ, ν⟩ := p
    obtain ⟨x₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
    rw [plaquetteDefect_readAtLevel_zero, plaquetteDefect_readAtLevel_zero]
    exact hHP x₀ μ ν (lt_of_mem_cutPlaquettes hp)
  refine ⟨fun c => ?_, ?_, ?_, ?_, hm⟩
  · have := ballRadius_pos hS
    simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using this
  · unfold IsHullState torusHotSites
    rw [hhot, hYt]
    exact hhull
  · intro X hX
    have hXs : X ⊆ (G.settingOf GasFamily.empty).support := subset_of_mem_chainComponents hX
    have hX' : X ∈ chainComponents R.range Yt := by
      rw [hYt] at hX
      exact hX
    have hXY : X ⊆ Yt := subset_of_mem_chainComponents hX'
    have e : R.clusterFactor (n * R.params.side) ((G.settingOf GasFamily.empty).field 0)
        (G.settingOf GasFamily.empty).support (G.settingOf GasFamily.empty).labelling X =
        R.clusterFactor (n * R.params.side) W Yt ωt X := by
      refine hS.hasExpansions.2.reads_class (n * R.params.side) hside _ _ _ _ _ _ X hXs hXY ?_ ?_
      · intro c h1 h2
        exact hval c (hcore _ (Finset.mem_union_right _ (hXY h1))) (hcore _ (Finset.mem_union_right _ (hXY h2)))
      · intro z hz hz' _
        have hns : z ∉ (GasFamily.empty : GasFamily R n).sites := by
          rw [sites_empty]
          simp
        show (if h : z ∈ (GasFamily.empty : GasFamily R n).sites then GasFamily.labelAt _ h else
          G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right h⟩) = _
        rw [dif_neg hns]
        exact getRight_eq_of_eq_inr (hlabel z hz') _
    rw [e]
    exact hΦ X hX'
  · have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hodd
    have hs0 : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => by
      show 0 < n
      omega
    rw [bases_settingOf_empty hS]
    apply baseLaw_ne_zero_of_mem
    have hb0 : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
      by_contra hn'
      apply hlaw
      unfold baseLaw
      rw [if_neg hn']
    have hIs := (Finset.mem_filter.mp hb0).2
    have hcorner : ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
        R.params.threshold ≤ curvature ((G.settingOf GasFamily.empty).field 0) x μ ν →
          ∀ z ∈ plaquetteVertices x μ ν, z ∈ G.anchorSites :=
      fun x μ ν hμ h z hz => hatY z (hWcorner x μ ν hμ ((hHP x μ ν hμ).mp h) z hz)
    have hgoal : IsBaseChoice (F := stepBlockFrame R.params.side n) R.params.baseDepth
        (hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
          (readAtLevel (stepBlockFrame R.params.side n) 0 W)) G.groundBases := by
      intro y
      obtain ⟨y₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one y
      by_cases hy : y₀ ∈ Z
      · have hcell : enclosingCell (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀)) =
            torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀ := by
          by_cases hc : nearbyLumps (hotLumps R.params.grid R.params.threshold
              (levelSites (stepBlockFrame R.params.side n) 0)
              (readAtLevel (stepBlockFrame R.params.side n) 0 W))
              (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) = ∅ ∨
              IsCrowded R.params.baseDepth (hotLumps R.params.grid R.params.threshold
              (levelSites (stepBlockFrame R.params.side n) 0)
              (readAtLevel (stepBlockFrame R.params.side n) 0 W))
              (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀)
          · rw [(hIs _).1 hc]
            exact enclosingCell_cellCentre hodd' _
          · exact BlockSites.enclosingCell_eq_of_mem_sitesBelow hodd' hs0 ((hIs _).2 hc).1
        obtain ⟨u, hu⟩ := torusSiteInFrame_surjective (m := n * R.params.side) (stepBlockFrame R.params.side n) 0
          stepBlockFrame_period_zero (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀))
        have hblk : parentBlock R.params.side u = y₀ := by
          have h1 := enclosingCell_torusSiteInFrame (L := R.params.side) (n := n) u
          rw [hu, hcell] at h1
          exact (torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one h1).symm
        have hon : toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side)
            (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀)) = u := by
          rw [← hu]
          funext k
          exact intCast_cast_intCast_cast (stepBlockFrame_period_zero k).symm (u k)
        have hby : G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) =
            b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) := by
          unfold GasGround.groundBases
          rw [toTorusSite_torusSiteInFrame hS, hstore, if_pos hy]
          show torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y₀ (baseOffset R b y₀)) = _
          unfold baseOffset
          rw [hon, ← hblk, blockSite_parentBlock_siteOffset, hblk, hu]
        rw [hby]
        exact hIs _
      · have hb := nearbyLumps_eq_empty_off_zone hS hcorner y₀ hy
        have hb' : nearbyLumps (hotLumps R.params.grid R.params.threshold
            (levelSites (stepBlockFrame R.params.side n) 0)
            (readAtLevel (stepBlockFrame R.params.side n) 0 W))
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) = ∅ :=
          Eq.mp (congrArg (fun H => nearbyLumps (F := stepBlockFrame R.params.side n) H
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) = ∅) hlumps) hb
        have hcen : G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) =
            cellCentre (F := stepBlockFrame R.params.side n) 0
              (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y₀) := by
          unfold GasGround.groundBases
          rw [toTorusSite_torusSiteInFrame hS, hstore, if_neg hy]
        exact ⟨fun _ => hcen, fun h => absurd (Or.inl hb') h⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Eq.mpr (congrArg (fun H => IsBaseChoice (F := stepBlockFrame R.params.side n) R.params.baseDepth H
      G.groundBases) hlumps) hgoal
end Main
theorem groundWeightAtEmpty_holds (hGood : coldPlaquette_of_small_frameDeviation) :
    GroundWeightAtEmpty := by
  intro T hT
  obtain ⟨y₀, h⟩ := exists_stepHypotheses_of_admissible T hT
  refine ⟨y₀, fun y hy R hOn _ n _ G hG => ?_⟩
  obtain ⟨Z, S, s₀, hS, hside⟩ := h y hy R hOn n G hG GasFamily.empty isGasFamily_empty
  rcases hG with hc | hh
  · exact hasWeightAt_empty_of_cold hS hGood hc
  · exact hasWeightAt_empty_of_hot hS hGood hside hh
end GroundWeight
end YangMills.Construction
end
