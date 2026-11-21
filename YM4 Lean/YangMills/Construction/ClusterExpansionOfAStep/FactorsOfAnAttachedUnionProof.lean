import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAnAttachedUnion
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCostProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepCosts RenormalizationStepParameters StepSettings TorusLumps TorusFields KeptRegion BlockPlaces
  TorusBalls StepFactors
namespace AttachedUnionFactors
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem markAt_restrict (q : CoarseState R n) (X : Finset (TorusSite n)) (y : TorusSite n) :
    (q.restrict X).markAt y = if y ∈ X then q.markAt y else none := by
  classical
  unfold CoarseState.markAt CoarseState.restrict
  by_cases hX : y ∈ X
  · by_cases hq : y ∈ q.1
    · have : y ∈ q.1 ∩ X := Finset.mem_inter.mpr ⟨hq, hX⟩
      simp [this, hX, hq]
    · have : y ∉ q.1 ∩ X := fun h => hq (Finset.mem_inter.mp h).1
      simp [this, hX, hq]
  · have : y ∉ q.1 ∩ X := fun h => hX (Finset.mem_inter.mp h).2
    simp [this, hX]
theorem labelAt_labeling (q : CoarseState R n) (z : q.labelSet) : q.labelAt z.1 = Sum.inr (q.labeling z) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.labelAt_eq_inr_labeling <;> assumption
section State
variable {C : Finset (TorusSite n)} {W : TorusField (n * R.params.side)}
  {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
  {bad : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n}
theorem markAt_coarseStateOf (y : TorusSite n) :
    (coarseStateOf R C W Yt ωt bad b).markAt y =
      if y ∈ storedBlocks R.params.side R.range bad Yt C then
        some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) W Yt ωt bad b y) else none := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.markAt_coarseStateOf <;> assumption
theorem labelAt_restrict_of_mem (X : Finset (TorusSite n)) {z : TorusSite (n * R.params.side)} (hz : z ∈ Yt)
    (hX : parentBlock R.params.side z ∈ X)
    (hZ : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C) :
    ((coarseStateOf R C W Yt ωt bad b).restrict X).labelAt z = Sum.inr (ωt ⟨z, hz⟩) := by
  classical
  unfold CoarseState.labelAt
  rw [markAt_restrict, if_pos hX, markAt_coarseStateOf, if_pos hZ]
  have hp : blockSite (L := R.params.side) (parentBlock R.params.side z) (siteOffset z) = z :=
    blockSite_parentBlock_siteOffset z
  simp only [blockConfigAt]
  rw [dif_pos (by rw [hp]; exact hz)]
  congr 2
  exact Subtype.ext hp
theorem labelAt_restrict_of_not_mem (X : Finset (TorusSite n)) {z : TorusSite (n * R.params.side)}
    (h : z ∉ Yt ∨ parentBlock R.params.side z ∉ X) :
    ((coarseStateOf R C W Yt ωt bad b).restrict X).labelAt z = Sum.inl () := by
  classical
  unfold CoarseState.labelAt
  rw [markAt_restrict]
  by_cases hX : parentBlock R.params.side z ∈ X
  · have hz : z ∉ Yt := h.resolve_right (not_not.mpr hX)
    rw [if_pos hX, markAt_coarseStateOf]
    by_cases hZ : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C
    · rw [if_pos hZ]
      have hp : blockSite (L := R.params.side) (parentBlock R.params.side z) (siteOffset z) = z :=
        blockSite_parentBlock_siteOffset z
      simp only [blockConfigAt]
      rw [dif_neg (by rw [hp]; exact hz)]
    · rw [if_neg hZ]
  · rw [if_neg hX]
theorem labelSet_restrict (X : Finset (TorusSite n))
    (hZ : ∀ z ∈ Yt, parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C) :
    ((coarseStateOf R C W Yt ωt bad b).restrict X).labelSet =
      (open Classical in Yt.filter fun z => parentBlock R.params.side z ∈ X) := by
  classical
  ext z
  simp only [CoarseState.labelSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    apply h
    refine labelAt_restrict_of_not_mem X ?_
    by_cases hz : z ∈ Yt
    · exact Or.inr fun hX => hc ⟨hz, hX⟩
    · exact Or.inl hz
  · rintro ⟨hz, hX⟩
    rw [labelAt_restrict_of_mem X hz hX (hZ z hz)]
    simp
theorem storedField_restrict (X : Finset (TorusSite n)) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (hX : parentBlock R.params.side x ∈ X)
    (hZ : parentBlock R.params.side x ∈ storedBlocks R.params.side R.range bad Yt C)
    (hZ' : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈
      storedBlocks R.params.side R.range bad Yt C) :
    ((coarseStateOf R C W Yt ωt bad b).restrict X).storedField x i = W x i := by
  classical
  unfold CoarseState.storedField CoarseState.fieldWithStoredLinks
  rw [markAt_restrict, if_pos hX, markAt_coarseStateOf, if_pos hZ]
  have hp : blockSite (L := R.params.side) (parentBlock R.params.side x) (siteOffset x) = x :=
    blockSite_parentBlock_siteOffset x
  simp only [blockConfigAt, hp, hZ', if_true]
end State
theorem chainComponents_eq_filter_of_closed {N : ℕ} [NeZero N] {r : ℕ} {S Y : Finset (TorusSite N)} (hS : S ⊆ Y)
    (hc : ∀ u ∈ S, ∀ v ∈ Y, supDist u v ≤ r → v ∈ S) :
    chainComponents r S = (open Classical in (chainComponents r Y).filter (· ⊆ S)) := by
  classical
  have hj : ∀ {y v : TorusSite N}, y ∈ S → ChainConnected r Y y v → ChainConnected r S y v := by
    intro y v hy h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hh hs ih =>
      have hb : _ ∈ S := chainConnected_mem hy ih
      exact ih.tail ⟨hb, hc _ hb _ hs.2.1 hs.2.2, hs.2.2⟩
  have hj' : ∀ {y v : TorusSite N}, ChainConnected r S y v → ChainConnected r Y y v := by
    intro y v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ⟨hS hs.1, hS hs.2.1, hs.2.2⟩
  have hjm : ∀ {y v : TorusSite N}, y ∈ S → ChainConnected r Y y v → v ∈ S :=
    fun hy h => chainConnected_mem hy (hj hy h)
  ext Xc
  rw [Finset.mem_filter, mem_chainComponents, mem_chainComponents]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have he : S.filter (ChainConnected r S y) = Y.filter (ChainConnected r Y y) := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hS h.1, hj' h.2⟩, fun h => ⟨hjm hy h.2, hj hy h.2⟩⟩
    refine ⟨⟨y, hS hy, he⟩, Finset.filter_subset _ _⟩
  · rintro ⟨⟨y, hy, rfl⟩, hsub⟩
    have hyS : y ∈ S := hsub (Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩)
    refine ⟨y, hyS, ?_⟩
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hjm hyS h.2, hj hyS h.2⟩, fun h => ⟨hS h.1, hj' h.2⟩⟩
theorem le_clusterRange_of_pow_le {x : ℝ} (A : ℕ) (hx : (A : ℝ) ^ 100 ≤ x) : A ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
theorem barrier_nonneg {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (u : ℝ) (h0 : 0 ≤ u) (h1 : u < ρ) :
    0 ≤ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoff_nonneg_of_lt <;> assumption
omit [NeZero n] in
theorem bondMark_mem_unit (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 := by
  unfold bondMark cutoffFactor
  split_ifs with h
  · refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have := barrier_nonneg hρ hp _ (norm_nonneg _) h
    linarith
  · exact ⟨le_refl _, zero_le_one⟩
omit [NeZero n] in
theorem blockBaseWeight_mem_unit (h : Finset (Finset ((stepBlockFrame R.params.side n).Site 0)))
    (y : (stepBlockFrame R.params.side n).Cell) (z : (stepBlockFrame R.params.side n).Site 0) :
    0 ≤ blockBaseWeight R.params h y z ∧ blockBaseWeight R.params h y z ≤ 1 := by
  classical
  unfold blockBaseWeight
  split_ifs with hz
  · have hc : 1 ≤ (baseSitesAt R.params.baseDepth h y).card := Finset.card_pos.mpr ⟨z, hz⟩
    have hc' : (1 : ℝ) ≤ ((baseSitesAt R.params.baseDepth h y).card : ℝ) := by exact_mod_cast hc
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hc'⟩
  · exact ⟨le_refl _, zero_le_one⟩
theorem markFactorProduct_mem_unit (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) :
    0 ≤ markFactorProduct V q X ∧ markFactorProduct V q X ≤ 1 := by
  classical
  unfold markFactorProduct
  have hb : ∀ b, 0 ≤ (if b ∈ (q.restrict X).storedBadBonds then 1 - bondMark R V (q.restrict X).storedField b
      else bondMark R V (q.restrict X).storedField b) ∧
      (if b ∈ (q.restrict X).storedBadBonds then 1 - bondMark R V (q.restrict X).storedField b
      else bondMark R V (q.restrict X).storedField b) ≤ 1 := by
    intro b
    obtain ⟨h0, h1⟩ := bondMark_mem_unit hρ hp V (q.restrict X).storedField b
    split_ifs
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨h0, h1⟩
  exact ⟨Finset.prod_nonneg fun b _ => (hb b).1, Finset.prod_le_one (fun b _ => (hb b).1) fun b _ => (hb b).2⟩
theorem baseFactorProduct_mem_unit (q : CoarseState R n) (X : Finset (TorusSite n)) :
    0 ≤ baseFactorProduct q X ∧ baseFactorProduct q X ≤ 1 := by
  unfold baseFactorProduct
  have hb : ∀ y, 0 ≤ (match (q.restrict X).markAt y with
      | some s => blockBaseWeight R.params
          (frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint))
      | none => (1 : ℝ)) ∧ (match (q.restrict X).markAt y with
      | some s => blockBaseWeight R.params
          (frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint))
      | none => (1 : ℝ)) ≤ 1 := by
    intro y
    cases (q.restrict X).markAt y with
    | none => exact ⟨zero_le_one, le_refl _⟩
    | some s => exact blockBaseWeight_mem_unit _ _ _
  exact ⟨Finset.prod_nonneg fun y _ => (hb y).1, Finset.prod_le_one (fun y _ => (hb y).1) fun y _ => (hb y).2⟩
theorem admissibilityIndicator_mem_unit (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) :
    0 ≤ admissibilityIndicator V q X ∧ admissibilityIndicator V q X ≤ 1 := by
  classical
  unfold admissibilityIndicator
  split_ifs
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨le_refl _, zero_le_one⟩
theorem coarseFactor_le (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (q : CoarseState R n) (X : Finset (TorusSite n)) (hl : 0 ≤ clusterFactorProduct q X) :
    0 ≤ coarseFactor V q X ∧ coarseFactor V q X ≤ clusterFactorProduct q X := by
  obtain ⟨t0, t1⟩ := admissibilityIndicator_mem_unit V q X
  obtain ⟨m0, m1⟩ := markFactorProduct_mem_unit hρ hp V q X
  obtain ⟨b0, b1⟩ := baseFactorProduct_mem_unit q X
  unfold coarseFactor
  refine ⟨by positivity, ?_⟩
  calc admissibilityIndicator V q X * clusterFactorProduct q X * markFactorProduct V q X * baseFactorProduct q X
      ≤ 1 * clusterFactorProduct q X * 1 * 1 := by gcongr
    _ = clusterFactorProduct q X := by ring
theorem clusterFactorProduct_restrict {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n} {C : Finset (TorusSite n)}
    (hrow : R.HasExpansions) (hbn : IsBlockTorusSide R.params (n * R.params.side)) (X : Finset (TorusSite n))
    (hZ : ∀ z ∈ Yt, parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C)
    (hcl : ∀ u ∈ (open Classical in Yt.filter fun z => parentBlock R.params.side z ∈ X), ∀ v ∈ Yt,
      supDist u v ≤ R.range → v ∈ (open Classical in Yt.filter fun z => parentBlock R.params.side z ∈ X)) :
    clusterFactorProduct (coarseStateOf R C W Yt ωt bad b) X =
      ∏ Xc ∈ (open Classical in (chainComponents R.range Yt).filter
          (· ⊆ (open Classical in Yt.filter fun z => parentBlock R.params.side z ∈ X))),
        R.clusterFactor (n * R.params.side) W Yt ωt Xc := by
  classical
  unfold clusterFactorProduct
  have hls := labelSet_restrict (R := R) (W := W) (ωt := ωt) (b := b) X hZ
  have hstep : ∀ Xc ∈ chainComponents R.range ((coarseStateOf R C W Yt ωt bad b).restrict X).labelSet,
      R.clusterFactor (n * R.params.side) ((coarseStateOf R C W Yt ωt bad b).restrict X).storedField
        ((coarseStateOf R C W Yt ωt bad b).restrict X).labelSet
        ((coarseStateOf R C W Yt ωt bad b).restrict X).labeling Xc =
      R.clusterFactor (n * R.params.side) W Yt ωt Xc := by
    intro Xc hXc
    have h1 := subset_of_mem_chainComponents hXc
    have h2 : ∀ z ∈ Xc, z ∈ Yt ∧ parentBlock R.params.side z ∈ X := fun z hz => by
      have := h1 hz
      rw [hls] at this
      exact Finset.mem_filter.mp this
    refine hrow.2.reads_class (n * R.params.side) hbn _ _ _ _ _ _ Xc h1 (fun z hz => (h2 z hz).1) ?_ ?_
    · intro c hc hc'
      exact storedField_restrict X (h2 _ hc).2 (hZ _ (h2 _ hc).1) (hZ _ (h2 _ hc').1)
    · intro z hz hz' hzX
      have e1 := labelAt_labeling ((coarseStateOf R C W Yt ωt bad b).restrict X) ⟨z, hz⟩
      have e2 := labelAt_restrict_of_mem (R := R) (W := W) (ωt := ωt) (bad := bad) (b := b) (C := C) X hz'
        (h2 z hzX).2 (hZ z hz')
      exact Sum.inr.inj (e1.symm.trans e2)
  rw [Finset.prod_congr rfl hstep, hls, chainComponents_eq_filter_of_closed (Finset.filter_subset _ _) hcl]
end AttachedUnionFactors
open AttachedUnionFactors in
theorem AttachedUnionFactors.attachedUnionFactorBound_holds : AttachedUnionFactorBound := by
  classical
  intro T hT
  refine ⟨max T.floorMin (((8 * T.side + 2 ^ 16 : ℕ) : ℝ) ^ 100),
    fun y hy R hR n _ hn V q W Yt ωt bad b P hV hW hst hatt hP hall => ?_⟩
  subst hst
  simp only [max_le_iff] at hy
  obtain ⟨a0, aBig⟩ := hy
  have hlet := hR.params_eq
  have hrow := hR.isStep.1
  have hfit : R.params.Admissible := hlet ▸ hT.fits y a0
  have hLe : R.params.side = T.side := by rw [hlet]; rfl
  have hbig : 8 * T.side + 2 ^ 16 ≤ R.range := le_clusterRange_of_pow_le _ (aBig.trans hR.le_coupling)
  have hd : KeptPartData R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) P :=
    { attached_eq := hatt
      subset_components := hP
      side_ge := hfit.L_ge
      side_odd := hfit.L_odd
      range_ge := by rw [hLe]; omega
      range_floor := by omega
      range_le := hR.isStep.2.2 }
  have hZ : ∀ z ∈ Yt, parentBlock R.params.side z ∈
      storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) := fun z hz =>
    parentBlock_mem_storedBlocks hd (mem_clusterSites_of_mem_support hd hz)
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have h1 : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hlet]; rfl
    rw [h1, hR.barrierFn_eq]
    exact hT.cut
  have hbn : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by
      have h1 := hn.2
      have h2 : R.params.n₀ ≤ n := by
        have := hfit.L_ge
        nlinarith
      have h3 : R.params.side * R.params.n₀ ≤ R.params.side * n := Nat.mul_le_mul_left _ h2
      linarith [Nat.mul_comm n R.params.side]⟩
  set q := coarseStateOf R (hotCoreSites R V) W Yt ωt bad b with hq
  have hcl : ∀ X ∈ chainComponents R.nextRange q.1, ∀ u ∈ Yt.filter (fun z => parentBlock R.params.side z ∈ X),
      ∀ v ∈ Yt, supDist u v ≤ R.range → v ∈ Yt.filter (fun z => parentBlock R.params.side z ∈ X) := by
    intro X hX u hu v hv huv
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    have hvY := storedBlocks_subset_coarseHull hd (hZ v hv)
    have hstep := (supDist_parentBlock_le_div_add_one R.params.side u v).trans
      (div_side_add_one_le_nextRange hd _ (by omega))
    exact Finset.mem_filter.mpr ⟨hv, mem_of_chainConnected_of_mem_chainComponents hX hu2 hvY
      (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hu2) hvY hstep)⟩
  have hlev : ∀ X ∈ P, clusterFactorProduct q X = ∏ Xc ∈ (chainComponents R.range Yt).filter
      (· ⊆ Yt.filter fun z => parentBlock R.params.side z ∈ X), R.clusterFactor (n * R.params.side) W Yt ωt Xc :=
    fun X hX => clusterFactorProduct_restrict hrow hbn X hZ (hcl X (hP hX))
  have hnn : ∀ X ∈ P, 0 ≤ clusterFactorProduct q X := fun X hX => by
    rw [hlev X hX]
    exact Finset.prod_nonneg fun Xc _ => hrow.2.factor_nonneg (n * R.params.side) hbn _ _ _ _
  have h1 : ∏ X ∈ P, coarseFactor V q X ≤ ∏ X ∈ P, clusterFactorProduct q X :=
    Finset.prod_le_prod (fun X hX => (coarseFactor_le hρ hcut V q X (hnn X hX)).1)
      fun X hX => (coarseFactor_le hρ hcut V q X (hnn X hX)).2
  refine h1.trans (le_of_eq ?_)
  rw [Finset.prod_congr rfl hlev, ← Finset.prod_biUnion]
  · refine Finset.prod_congr ?_ fun _ _ => rfl
    ext Xc
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨X, hX, hXc, hsub⟩
      refine ⟨hXc, fun v hv => ?_⟩
      obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp (hsub hv)
      exact (mem_attachedInBlocks_iff hd).mpr ⟨mem_clusterSites_of_mem_support hd hv1,
        Finset.mem_biUnion.mpr ⟨X, hX, hv2⟩⟩
    · rintro ⟨hXc, hsub⟩
      obtain ⟨y₀, hy₀, rfl⟩ := mem_chainComponents.mp hXc
      have hy₀X : y₀ ∈ Yt.filter (ChainConnected R.range Yt y₀) :=
        Finset.mem_filter.mpr ⟨hy₀, Relation.ReflTransGen.refl⟩
      obtain ⟨X, hX, hbX⟩ := Finset.mem_biUnion.mp ((mem_attachedInBlocks_iff hd).mp (hsub hy₀X)).2
      refine ⟨X, hX, hXc, fun v hv => ?_⟩
      have hj : ChainConnected R.range Yt y₀ v := (Finset.mem_filter.mp hv).2
      have hall' : ∀ w, ChainConnected R.range Yt y₀ w → w ∈ Yt.filter fun z => parentBlock R.params.side z ∈ X := by
        intro w hw
        induction hw with
        | refl => exact Finset.mem_filter.mpr ⟨hy₀, hbX⟩
        | tail _ hs ih => exact hcl X (hP hX) _ ih _ hs.2.1 hs.2.2
      exact hall' v hj
  · intro X hX X' hX' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro Xc h1' h2'
    obtain ⟨h3, h4⟩ := Finset.mem_filter.mp h1'
    obtain ⟨_, h5⟩ := Finset.mem_filter.mp h2'
    obtain ⟨y₀, hy₀, rfl⟩ := mem_chainComponents.mp h3
    have hy₀X : y₀ ∈ Yt.filter (ChainConnected R.range Yt y₀) :=
      Finset.mem_filter.mpr ⟨hy₀, Relation.ReflTransGen.refl⟩
    have e1 := (Finset.mem_filter.mp (h4 hy₀X)).2
    have e2 := (Finset.mem_filter.mp (h5 hy₀X)).2
    exact hne (eq_of_chainConnected_of_mem_chainComponents (hP hX) (hP hX') e1 e2 Relation.ReflTransGen.refl)
end YangMills.Construction
