import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfAGround
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAFamily
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
def StatesAllowedOfWeight : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n), G.IsAdmissibleGround →
      ∀ γ : StepGas.GasFamily R n, G.IsGasFamily γ → ∀ η, G.HasWeightAt γ η →
        ∀ (θ : StepGas.GasSupport R n) (h : γ.Occupies θ), G.IsAllowed θ (γ.state h)
end YangMills.Construction.ClusterExpansionOfAStep
end

set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages Holes HoleSavings LumpContours FamilyRestrictions TorusLumps TorusFields StepGas
  StepSettings RenormalizationStepParameters StepCosts StepMarks BlockZones BlockTrees BlockPlaces TopLevelSites
namespace WeightAdmissible
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {γ : GasFamily R n}
open Classical in
theorem mem_chainComponents_of_separated_subset {m : ℕ} [NeZero m] {r : ℕ} {Y Y₁ X : Finset (TorusSite m)}
    (hsub : Y₁ ⊆ Y) (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < supDist u v) (hX : X ∈ chainComponents r Y₁) :
    X ∈ chainComponents r Y := by
  obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
  have hz₁ : z ∈ Y₁ := subset_of_mem_chainComponents hX hz
  rw [eq_filter_of_mem_chainComponents hX hz]
  refine mem_chainComponents.mpr ⟨z, hsub hz₁, ?_⟩
  ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hsub h1, chainConnected_mono hsub h2⟩
  · rintro ⟨_, hj⟩
    exact chainConnected_of_separated hsep hz₁ hj
theorem isGasFamily_single (hB : IsReadable G γ) {θ : GasSupport R n} (h : γ.Occupies θ) (s : SupportState θ) :
    G.IsGasFamily (GasFamily.single θ s) := by
  refine ⟨fun θ' h' => ?_, fun θ₁ θ₂ h₁ h₂ e => ?_⟩
  · rw [(occupies_single_iff s).mp h']
    exact hB.isFamily.1 θ h
  · exact absurd (((occupies_single_iff s).mp h₁).trans ((occupies_single_iff s).mp h₂).symm) e
theorem isReadable_single (hB : IsReadable G γ) {θ : GasSupport R n} (h : γ.Occupies θ) (s : SupportState θ) :
    IsReadable G (GasFamily.single θ s) :=
  { hB with isFamily := isGasFamily_single hB h s }
theorem mem_support_single_of_near (hB : IsReadable G γ) {θ : GasSupport R n} (h : γ.Occupies θ)
    {a z : TorusSite (n * R.params.side)}
    (ha : a ∈ θ.sites) (hd : supDist a z ≤ 9 * R.range) (hz : z ∈ (G.settingOf γ).support) :
    z ∈ (G.settingOf (GasFamily.single θ (γ.state h))).support := by
  rcases Finset.mem_union.mp hz with b | b
  · exact Finset.mem_union_left _ b
  · obtain ⟨θ', h', hzθ⟩ := mem_sites_iff.mp b
    by_cases e : θ' = θ
    · subst e
      exact Finset.mem_union_right _ ((mem_sites_single_iff _).mpr hzθ)
    · have ap := hB.isFamily.2 θ θ' h h' (Ne.symm e) a ha z (mem_sites_of_mem_snd θ' hzθ)
      omega
theorem isHullState_single (hB : IsReadable G γ)
    (hull0 : IsHullState R.params R.range (G.frameField γ) (G.settingOf γ).support)
    {θ : GasSupport R n} (h : γ.Occupies θ) :
    IsHullState R.params R.range (G.frameField (GasFamily.single θ (γ.state h)))
      (G.settingOf (GasFamily.single θ (γ.state h))).support := by
  classical
  have hfar := hB.far
  have hbig := hB.big
  have hB₁ := isReadable_single hB h (γ.state h)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
    obtain ⟨l, hl, hxl⟩ := mem_torusHotSites_iff.mp hx
    obtain ⟨p, μ, ν, hμ, hs, z', hz', hlz⟩ := (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mp hl
    have hzl : z' ∈ l := by
      rw [hlz]
      exact mem_torusLumpOf_self z'
    by_cases hc : ∃ u, supDist p u ≤ 2 ∧ parentBlock R.params.side u ∈ θ.core
    · obtain ⟨u, hu, hcore⟩ := hc
      have ag := agreeNear_single_of_mem_core hB h (x := p) (d := 2) hcore (by omega)
      have hl' : l ∈ torusHotLumps R.params (G.frameField γ) :=
        (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mpr ⟨p, μ, ν, hμ, by
          rw [curvature_eq_of_agreeNear (side_odd hB) hB.two_le ag]
          exact hs, z', hz', hlz⟩
      have hzY := hull0.1 ((mem_thickening _ _ _).mpr ⟨x, mem_torusHotSites_iff.mpr ⟨l, hl', hxl⟩, hzx⟩)
      obtain ⟨a, ha, had⟩ := exists_site_near_of_mem_core hcore
      have h1 := supDist_lt_of_mem_torusHotLumps hB.admissible (side_dvd hB) hl hzl hxl
      have h2 := supDist_le_two_of_mem_plaquetteVertices hz'
      have t1 := supDist_triangle a u z
      have t2 := supDist_triangle u p z
      have t3 := supDist_triangle p z' z
      have t4 := supDist_triangle z' x z
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm a u] at t1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm u p] at t2
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm x z] at t4
      exact mem_support_single_of_near hB h ha (by omega) hzY
    · have ag : AgreeNear (GasFamily.single θ (γ.state h)) GasFamily.empty p 2 :=
        agreeNear_empty_of_forall fun θ' h' u hu hcore =>
          hc ⟨u, hu, (occupies_single_iff _).mp h' ▸ hcore⟩
      have hl' : l ∈ torusHotLumps R.params (G.frameField GasFamily.empty) :=
        (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mpr ⟨p, μ, ν, hμ, by
          rw [← curvature_eq_of_agreeNear (side_odd hB) hB.two_le ag]
          exact hs, z', hz', hlz⟩
      have h1 := (isHullState_empty hB).1 ((mem_thickening _ _ _).mpr ⟨x, mem_torusHotSites_iff.mpr ⟨l, hl', hxl⟩, hzx⟩)
      rcases Finset.mem_union.mp h1 with a | a
      · exact Finset.mem_union_left _ a
      · exact absurd a not_mem_sites_empty
  · intro X hX
    obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
    rcases Finset.mem_union.mp (subset_of_mem_chainComponents hX hz) with a | a
    · obtain ⟨l, hl, hw⟩ := (isHullState_empty hB).2 X (mem_chainComponents_recorded hB₁ hX hz a).1
      exact ⟨l, mem_torusHotLumps_of_empty hB₁ hl, hw⟩
    · have hθ : z ∈ θ.2 := (mem_sites_single_iff _).mp a
      have hsub : (G.settingOf (GasFamily.single θ (γ.state h))).support ⊆ (G.settingOf γ).support :=
        fun w hw => by
          rcases Finset.mem_union.mp hw with b | b
          · exact Finset.mem_union_left _ b
          · exact Finset.mem_union_right _ (mem_sites_iff.mpr ⟨θ, h, (mem_sites_single_iff _).mp b⟩)
      have hX' : X ∈ chainComponents R.range (G.settingOf γ).support :=
        mem_chainComponents_of_separated_subset hsub (fun u hu v hv hn => by
          have hv1 : v ∉ G.recordedSites := fun c => hn (Finset.mem_union_left _ c)
          have hv2 : v ∉ θ.2 := fun c => hn (Finset.mem_union_right _ ((mem_sites_single_iff _).mpr c))
          rcases Finset.mem_union.mp hv with b | b
          · exact absurd b hv1
          · obtain ⟨θ', h', hvθ⟩ := mem_sites_iff.mp b
            have e : θ ≠ θ' := fun e => hv2 (e ▸ hvθ)
            rcases Finset.mem_union.mp hu with c | c
            · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
              exact range_lt_supDist_recorded hB h' hvθ c
            · exact range_lt_supDist_of_ne hB h h' e ((mem_sites_single_iff _).mp c) hvθ) hX
      obtain ⟨l, hl, w, hw⟩ := hull0.2 X hX'
      obtain ⟨hwl, hwX⟩ := Finset.mem_inter.mp hw
      have hh₁ := (mem_chainComponents_single hB h hX' hz hθ).2.1
      obtain ⟨p, μ, ν, hμ, hs, z', hz', hlz⟩ :=
        (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mp hl
      have hzl : z' ∈ l := by
        rw [hlz]
        exact mem_torusLumpOf_self z'
      have h1 := supDist_lt_of_mem_torusHotLumps hB.admissible (side_dvd hB) hl hzl hwl
      have h2 := supDist_le_two_of_mem_plaquetteVertices hz'
      have t1 := supDist_triangle p z' w
      have ag := agreeNear_single_of_mem_sites hB h (x := p) (d := 2) (mem_sites_of_mem_snd θ (hh₁ hwX)) (by omega)
      exact ⟨l, (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mpr ⟨p, μ, ν, hμ, by
        rw [← curvature_eq_of_agreeNear (side_odd hB) hB.two_le ag]
        exact hs, z', hz', hlz⟩, w, hw⟩
theorem single_state {θ : GasSupport R n} (s : SupportState θ) (h : (GasFamily.single θ s).Occupies θ) :
    (GasFamily.single θ s).state h = s := by apply _root_.YangMills.Construction.InBoxTransfer.state_single <;> assumption
theorem baseAt_single {θ : GasSupport R n} (s : SupportState θ) {y : TorusSite n} (hy : y ∈ θ.core) :
    (GasFamily.single θ s).baseAt y = Sum.inr (s.2.2 ⟨y, hy⟩) := by
  classical
  have hs : (GasFamily.single θ s).Occupies θ := (occupies_single_iff s).mpr rfl
  have hex : ∃ θ', (GasFamily.single θ s).Occupies θ' ∧ y ∈ θ'.core := ⟨θ, hs, hy⟩
  unfold GasFamily.baseAt
  rw [dif_pos hex]
  have he : hex.choose = θ := (occupies_single_iff s).mp hex.choose_spec.1
  rw [GasFamily.state_base_congr _ he hex.choose_spec.1 hs hex.choose_spec.2 hy, single_state]
theorem isHullState_single_of_occupies (hB : IsReadable G γ)
    (hull0 : IsHullState R.params R.range (G.frameField γ) (G.settingOf γ).support)
    {θ : GasSupport R n} (h : γ.Occupies θ) (θ' : GasSupport R n) (h' : (GasFamily.single θ (γ.state h)).Occupies θ') :
    IsHullState R.params R.range (G.frameField (GasFamily.single θ' ((GasFamily.single θ (γ.state h)).state h')))
      (G.settingOf (GasFamily.single θ' ((GasFamily.single θ (γ.state h)).state h'))).support := by
  obtain rfl := (occupies_single_iff _).mp h'
  rw [single_state]
  exact isHullState_single hB hull0 h
theorem not_mem_free_and_bad_of_coreBond (hB : IsReadable G γ) {θ : GasSupport R n} (h : γ.Occupies θ)
    {b : TorusBond (n * R.params.side)}
    (hst : b ∈ θ.coreBonds) (hm : b ∈ markedBonds R G.cut) (hb : b ∉ θ.1) :
    b ∉ (G.settingOf γ).free ∧ b ∉ (G.settingOf γ).bad := by
  classical
  have hfar := hB.far
  obtain ⟨a, ha, had⟩ := exists_site_near_of_mem_core (Finset.mem_filter.mp hst).2.1
  refine ⟨fun hf => ?_, fun hbad => ?_⟩
  · have h1 := (mem_free_settingOf hf).2.2
    unfold GasFamily.fieldAt at h1
    rw [dif_pos ⟨θ, h, hst⟩] at h1
    cases h1
  · have h1 : b ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst ∪
      (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut := hbad
    rcases Finset.mem_union.mp h1 with h2 | h2
    · rcases Finset.mem_union.mp h2 with h3 | h3
      · have hat : b.1 ∈ G.anchorSites := by
          unfold GasGround.anchorSites
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h3))
        have := (hB.isFamily.1 θ h).far_from_anchor a ha _ hat
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at had
        omega
      · obtain ⟨θ', hθ', hb'⟩ := Finset.mem_biUnion.mp h3
        have h' := (Finset.mem_filter.mp hθ').2
        by_cases e : θ' = θ
        · subst e
          exact hb hb'
        · have := hB.isFamily.2 θ θ' h h' (Ne.symm e) a ha b.1
            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb'))
          rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at had
          omega
    · exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp h2).2
end WeightAdmissible
open WeightAdmissible in
theorem statesAllowedOfWeight_of (hSw : SettingAdmissibleOfHasWeight) (hGw : GroundWeightAtEmpty)
    (hf1 : CouplingFloorExists) : StatesAllowedOfWeight := by
  classical
  intro T hT
  obtain ⟨y₁, hSw⟩ := hSw T hT
  obtain ⟨y₂, hGw⟩ := hGw T hT
  obtain ⟨y₃, hf1⟩ := hf1 1 (64 * T.side + 2 ^ 16) T.rt one_pos
  refine ⟨max y₁ (max y₂ (max y₃ T.floorMin)), fun y hy R hR hx' n _ G hG γ hγ η hw θ h => ?_⟩
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : y₂ ≤ y := le_trans (by simp) hy
  have b₃ : y₃ ≤ y := le_trans (by simp) hy
  have b₄ : T.floorMin ≤ y := le_trans (by simp) hy
  have hx := hR.le_coupling
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₄
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hrange := (hf1 R.coupling (b₃.trans hx)).1
  have hrr : R.range = clusterRange R.coupling := rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    rw [eL, hrr]
    omega
  have hbig : 2 ^ 16 ≤ R.range := by
    rw [hrr]
    omega
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG with g | g
    · exact g.n₀_le
    · have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      exact (Nat.le_mul_of_pos_left _ hL).trans g.isBlockSide.2
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hB : IsReadable G γ :=
    { isFamily := hγ, admissible := hfit, hasExpansions := hR.isStep.1, blockSide := hside, two_le := hn2,
      far := hfar, big := hbig
      groundWeight := hGw y b₂ R hR hx' n G hG
      exists_zone := exists_isAdmissibleZone G hG }
  have hs := hSw y b₁ R hR hx' n G hG γ hγ η hw
  have hin0 : (G.settingOf γ).InBalls 0 := fun b => by
    have hρ : 0 ≤ R.ballRadius := by
      have := hfit.σ_pos
      unfold StepSetup.ballRadius
      positivity
    simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using hρ
  have hz := field_zero_settingOf (G := G) (γ := γ) hfit.L_odd hn2
  have hull0 : IsHullState R.params R.range (G.frameField γ) (G.settingOf γ).support := by
    rw [← hz]
    exact hs.isHull 0 hin0
  have fac0 : ∀ X ∈ chainComponents R.range (G.settingOf γ).support,
      R.clusterFactor (n * R.params.side) (G.frameField γ) (G.settingOf γ).support (G.settingOf γ).labelling X ≠ 0 := by
    rw [← hz]
    exact hs.factor_ne_zero 0 hin0
  have hB₁ := isReadable_single hB h (γ.state h)
  refine ⟨isHullState_single hB hull0 h, fun X hX => ?_, fun b hb hnb => ?_, fun c₀ hy => ?_⟩
  · have hθs : (θ.2 : Finset (TorusSite (n * R.params.side))) ⊆ (G.settingOf γ).support := fun w hw =>
      Finset.mem_union_right _ (mem_sites_iff.mpr ⟨θ, h, hw⟩)
    have hX' : X ∈ chainComponents R.range (G.settingOf γ).support :=
      mem_chainComponents_of_separated_subset hθs (fun u hu v hv hn => by
        rcases Finset.mem_union.mp hv with b | b
        · exact range_lt_supDist_recorded hB h hu b
        · obtain ⟨θ', h', hvθ⟩ := mem_sites_iff.mp b
          exact range_lt_supDist_of_ne hB h h' (fun e => hn (e ▸ hvθ)) hu hvθ) hX
    have hXθ : ∀ z ∈ X, z ∈ θ.2 := fun z hz => subset_of_mem_chainComponents hX hz
    have hX₁ : X ⊆ (G.settingOf (GasFamily.single θ (γ.state h))).support := fun z hz =>
      Finset.mem_union_right _ ((mem_sites_single_iff _).mpr (hXθ z hz))
    have e : R.clusterFactor (n * R.params.side) (G.frameField γ) (G.settingOf γ).support
          (G.settingOf γ).labelling X =
        R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ (γ.state h)))
          (G.settingOf (GasFamily.single θ (γ.state h))).support
          (G.settingOf (GasFamily.single θ (γ.state h))).labelling X := by
      refine hB.hasExpansions.2.reads_class (n * R.params.side) hB.blockSide _ _ _ _ _ _ X
        (fun z hz => subset_of_mem_chainComponents hX' hz) hX₁ ?_ ?_
      · intro b hb _
        have ag := agreeNear_single_of_mem_sites hB h (x := b.1) (d := 1)
          (mem_sites_of_mem_snd θ (hXθ _ hb)) (by rw [supDist_self]; omega)
        exact frameField_eq_of_agreeNear (side_odd hB) hB.two_le ag b.2 (by rw [supDist_self])
      · intro w hw hw' hwX
        have ag := agreeNear_single_of_mem_sites hB h (x := w) (d := 0)
          (mem_sites_of_mem_snd θ (hXθ _ hwX)) (by rw [supDist_self]; omega)
        exact labelling_congr _ _ fun θ' hθ => ag θ' w (by rw [supDist_self])
          (parentBlock_mem_core θ' (mem_sites_of_mem_snd θ' hθ) (by rw [supDist_self]; omega))
    rw [← e]
    exact fac0 X hX'
  · obtain ⟨hst, hm⟩ := Finset.mem_inter.mp hb
    obtain ⟨f1, f2⟩ := not_mem_free_and_bad_of_coreBond hB h hst hm hnb
    have hc : b ∈ chartBonds R.params.side n := (Finset.mem_filter.mp hm).1
    have hmark := hs.cutoff_ne_zero b hc f1 f2
    have ag := agreeNear_single_of_mem_core hB h (v := b.1) (x := b.1) (d := R.params.side + 3)
      (Finset.mem_filter.mp hst).2.1 (by rw [supDist_self]; omega)
    unfold bondMark
    rw [← chartCoord_eq_of_agreeNear hfit.L_odd hn2 ag]
    exact hmark
  · have hb₁ : IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h))))
        (G.settingOf (GasFamily.single θ (γ.state h))).bases := by
      apply isBaseChoice_of_local
      intro c
      obtain ⟨d₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one c
      by_cases hc : d₀ ∈ θ.core
      · refine ⟨stepHotLumps R.params (G.frameField γ), (G.settingOf γ).bases, hs.isBaseChoice,
          (nearbyLumps_eq_single hB h hc).symm, bases_settingOf_congr ?_⟩
        intro θ' hθ'
        obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = d₀ :=
          ⟨blockSite d₀ (fun _ => 0), parentBlock_blockSite _ _⟩
        have ag := agreeNear_single_of_mem_core hB h (x := v) (d := 0) (v := v) (by rw [hv]; exact hc)
          (by rw [supDist_self]; omega)
        exact (ag θ' v (by rw [supDist_self]) (by rw [hv]; exact hθ')).symm
      · have h0 := hB.groundWeight.baseLaw_ne_zero
        rw [field_zero_settingOf hfit.L_odd hn2] at h0
        refine ⟨_, _, isBaseChoice_of_baseLaw_ne_zero h0,
          nearbyLumps_eq_empty hB₁ (isHullState_single_of_occupies hB hull0 h)
            (fun θ' h' => (occupies_single_iff _).mp h' ▸ hc), bases_settingOf_congr ?_⟩
        intro θ' hθ'
        show GasFamily.single θ (γ.state h) θ' = Sum.inl ()
        exact apply_eq_inl_of_not_occupies fun h' => hc ((occupies_single_iff _).mp h' ▸ hθ')
    have hmem : (G.settingOf (GasFamily.single θ (γ.state h))).bases ∈
        baseChoices R.params
          (readAtLevel (stepBlockFrame R.params.side n) 0 (G.frameField (GasFamily.single θ (γ.state h)))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₁⟩
    have hcell : (G.settingOf (GasFamily.single θ (γ.state h))).bases
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
        frameBlockSite R.params.side n c₀ ((γ.state h).2.2 ⟨c₀, hy⟩) := by
      have e : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) = c₀ :=
        toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_one i) c₀
      show (match (GasFamily.single θ (γ.state h)).baseAt
          (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) with
        | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
            (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) o
        | Sum.inl _ => G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) = _
      rw [e, baseAt_single _ hy]
    unfold baseUniformWeight
    rw [if_pos hmem]
    refine one_div_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨(γ.state h).2.2 ⟨c₀, hy⟩, ?_⟩))
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← hcell]
    have hup : Function.update (G.settingOf (GasFamily.single θ (γ.state h))).bases
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)
        ((G.settingOf (GasFamily.single θ (γ.state h))).bases
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) =
        (G.settingOf (GasFamily.single θ (γ.state h))).bases := Function.update_eq_self _ _
    rw [hup]
    exact hmem
end YangMills.Construction.ClusterExpansionOfAStep
end
